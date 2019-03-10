#include <linux/module.h>
#include <linux/types.h>
#include <linux/kernel.h>
#include <linux/jiffies.h>
#include <linux/string.h>
#include <linux/in.h>
#include <linux/errno.h>
#include <linux/init.h>
#include <linux/skbuff.h>
#include <linux/jhash.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <net/netlink.h>
#include <net/pkt_sched.h>
#include <net/pkt_cls.h>
#include <net/inet_ecn.h>

#define QUEUE_THRESHOLD 16384
#define DQCOUNT_INVALID -1
#define MAX_PROB 0xffffffffffffffff
#define PIE_SCALE 8

struct fq_pie_stats {
	u32 packets_in;		/* total number of packets enqueued */
	u32 dropped;		/* packets dropped due to fq_pie action */
	u32 overlimit;		/* dropped due to lack of space in queue */
	u32 ecn_mark;		/* packets marked with ECN */
	u32 new_flow_count; /* number of time packets created a new flow */
};

struct fq_pie_params {
	psched_time_t target;	/* user specified target delay in pschedtime */
	u32 tupdate;		/* timer frequency (in jiffies) */
	u32 limit;		/* number of packets that can be enqueued */
	u32 alpha;		/* alpha and beta are between 0 and 32 */
	u32 beta;		/* and are used for shift relative to 1 */
	bool ecn;		/* true if ecn is enabled */
	bool bytemode;		/* to scale drop early prob based on pkt size */
	u32 ecn_prob;
	u32 flows_cnt;
};

/* variables used */
struct pie_vars {
	u64 prob;		/* probability but scaled by u64 limit. */
	psched_time_t burst_time;
	psched_time_t qdelay;
	psched_time_t qdelay_old;
	u64 dq_count;		/* measured in bytes */
	psched_time_t dq_tstamp;	/* drain rate */
	u64 accu_prob;		/* accumulated drop probability */
	u32 avg_dq_rate;	/* bytes per pschedtime tick,scaled */
	u32 qlen_old;		/* in bytes */
	u8 accu_prob_overflows;	/* overflows of accu_prob */
};

/* statistics gathering */
struct pie_stats {
	u32 packets_in;		/* total number of packets enqueued */
	u32 dropped;		/* packets dropped due to pie_action */
	u32 overlimit;		/* dropped due to lack of space in queue */
	u32 maxq;		/* maximum queue size */
	u32 ecn_mark;		/* packets marked with ECN */
};

struct fq_pie_flow {
	struct sk_buff *head;
	struct sk_buff *tail;
	struct list_head flowchain;
	s32 deficit;
	u32 backlog;
	u32 qlen;
	struct pie_vars vars;
	struct pie_stats stats;
};

struct fq_pie_sched_data {
	u32 quantum;
	struct fq_pie_flow *flows;
	struct fq_pie_params params;
	struct fq_pie_stats stats;
	struct Qdisc *sch;
	struct timer_list adapt_timer;
	struct list_head old_flows;
	struct list_head new_flows;
};

static void fq_pie_params_init(struct fq_pie_params *params)
{
	params->alpha = 2;
	params->beta = 20;
	params->tupdate = usecs_to_jiffies(15 * USEC_PER_MSEC);	/* 15 ms */
	params->limit = 1000;	/* default of 1000 packets */
	params->target = PSCHED_NS2TICKS(15 * NSEC_PER_MSEC);	/* 15 ms */
	params->ecn = false;
	params->bytemode = false;
}

static void pie_vars_init(struct pie_vars *vars)
{
	vars->dq_count = DQCOUNT_INVALID;
	vars->accu_prob = 0;
	vars->avg_dq_rate = 0;
	/* default of 150 ms in pschedtime */
	vars->burst_time = PSCHED_NS2TICKS(150 * NSEC_PER_MSEC);
	vars->accu_prob_overflows = 0;
}

static bool drop_early(struct Qdisc *sch, u32 packet_size, struct fq_pie_flow *flow)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	u64 rnd;
	u64 local_prob = flow->vars.prob;
	u32 mtu = psched_mtu(qdisc_dev(sch));

	/* If there is still burst allowance left skip random early drop */
	if (flow->vars.burst_time > 0)
		return false;

	/* If current delay is less than half of target, and
	 * if drop prob is low already, disable early_drop
	 */
	if ((flow->vars.qdelay < q->params.target / 2) &&
	    (flow->vars.prob < MAX_PROB / 5))
		return false;

	/* If we have fewer than 2 mtu-sized packets, disable drop_early,
	 * similar to min_th in RED
	 */
	if (flow->backlog < 2 * mtu)
		return false;

	/* If bytemode is turned on, use packet size to compute new
	 * probablity. Smaller packets will have lower drop prob in this case
	 */
	if (q->params.bytemode && packet_size <= mtu)
		local_prob = (u64)packet_size * div_u64(local_prob, mtu);
	else
		local_prob = flow->vars.prob;

	if (local_prob == 0) {
		flow->vars.accu_prob = 0;
		flow->vars.accu_prob_overflows = 0;
	}

	if (local_prob > MAX_PROB - flow->vars.accu_prob)
		flow->vars.accu_prob_overflows++;

	flow->vars.accu_prob += local_prob;

	if (flow->vars.accu_prob_overflows == 0 &&
	    flow->vars.accu_prob < (MAX_PROB / 100) * 85)
		return false;
	if (flow->vars.accu_prob_overflows == 8 &&
	    flow->vars.accu_prob >= MAX_PROB / 2)
		return true;

	prandom_bytes(&rnd, 8);
	if (rnd < local_prob) {
		flow->vars.accu_prob = 0;
		flow->vars.accu_prob_overflows = 0;
		return true;
	}

	return false;
}

static unsigned int fq_pie_hash(const struct fq_pie_sched_data *q,
				struct sk_buff *skb)
{
	return reciprocal_scale(skb_get_hash(skb), q->params.flows_cnt);
}

static unsigned int fq_pie_classify(struct sk_buff *skb, struct Qdisc *sch,
				    int *qerr)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);

	return fq_pie_hash(q, skb) + 1;
}

static inline void flow_queue_add(struct fq_pie_flow *flow,
				  struct sk_buff *skb)
{
	if (!flow->head)
		flow->head = skb;
	else
		flow->tail->next = skb;
	flow->tail = skb;
	skb->next = NULL;
}

static int fq_pie_qdisc_enqueue(struct sk_buff *skb, struct Qdisc *sch,
				struct sk_buff **to_free)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	struct fq_pie_flow *sel_flow;
	int uninitialized_var(ret);
	u32 uninitialized_var(pkt_len);
	u32 idx;
	u8 enqueue = false;

	idx = fq_pie_classify(skb, sch, &ret);
	if (idx == 0) {
		if (ret & __NET_XMIT_BYPASS)
			qdisc_qstats_drop(sch);
		__qdisc_drop(skb, to_free);
		return ret;
	}
	idx--;
	sel_flow = &q->flows[idx];

	if (unlikely(qdisc_qlen(sch) >= sch->limit)) {
		q->stats.overlimit++;
		sel_flow->stats.overlimit++;
		goto out;
	}

	if (!drop_early(sch, skb->len, sel_flow)) {
		enqueue = true;
	} else if (q->params.ecn &&
		   sel_flow->vars.prob <= (MAX_PROB / 100) * q->params.ecn_prob &&
		   INET_ECN_set_ce(skb)) {
		/* If packet is ecn capable, mark it if drop probability
		 * is lower than the parameter ecn_prob, else drop it.
		 */
		q->stats.ecn_mark++;
		sel_flow->stats.ecn_mark++;
		enqueue = true;
	}
	if (enqueue) {
		pkt_len = qdisc_pkt_len(skb);
		q->stats.packets_in++;
		sch->qstats.backlog += pkt_len;
		sch->q.qlen++;
		flow_queue_add(sel_flow, skb);
		if (list_empty(&sel_flow->flowchain)) {
			list_add_tail(&sel_flow->flowchain, &q->new_flows);
			q->stats.new_flow_count++;
			sel_flow->deficit = q->quantum;
			sel_flow->stats.dropped = 0;
			sel_flow->qlen = 0;
			sel_flow->backlog = 0;
		}
		sel_flow->qlen++;
		sel_flow->stats.packets_in++;
		sel_flow->backlog += pkt_len;
		return NET_XMIT_SUCCESS;
	}
out:
	q->stats.dropped++;
	sel_flow->stats.dropped++;
	return qdisc_drop(skb, sch, to_free);
}

static inline struct sk_buff *dequeue_head(struct fq_pie_flow *flow)
{
	struct sk_buff *skb = flow->head;

	flow->head = skb->next;
	skb->next = NULL;
	return skb;
}

static void pie_process_dequeue(struct Qdisc *sch, struct sk_buff *skb, struct fq_pie_flow *flow)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	int qlen = flow->backlog;	/* current queue size in bytes */

	/* If current queue is about 10 packets or more and dq_count is unset
	 * we have enough packets to calculate the drain rate. Save
	 * current time as dq_tstamp and start measurement cycle.
	 */
	if (qlen >= QUEUE_THRESHOLD && flow->vars.dq_count == DQCOUNT_INVALID) {
		flow->vars.dq_tstamp = psched_get_time();
		flow->vars.dq_count = 0;
	}

	/* Calculate the average drain rate from this value.  If queue length
	 * has receded to a small value viz., <= QUEUE_THRESHOLD bytes,reset
	 * the dq_count to -1 as we don't have enough packets to calculate the
	 * drain rate anymore The following if block is entered only when we
	 * have a substantial queue built up (QUEUE_THRESHOLD bytes or more)
	 * and we calculate the drain rate for the threshold here.  dq_count is
	 * in bytes, time difference in psched_time, hence rate is in
	 * bytes/psched_time.
	 */
	if (flow->vars.dq_count != DQCOUNT_INVALID) {
		flow->vars.dq_count += skb->len;

		if (flow->vars.dq_count >= QUEUE_THRESHOLD) {
			psched_time_t now = psched_get_time();
			u32 dtime = now - flow->vars.dq_tstamp;
			u32 count = flow->vars.dq_count << PIE_SCALE;

			if (dtime == 0)
				return;

			count = count / dtime;

			if (flow->vars.avg_dq_rate == 0)
				flow->vars.avg_dq_rate = count;
			else
				flow->vars.avg_dq_rate =
				    (flow->vars.avg_dq_rate -
				     (flow->vars.avg_dq_rate >> 3)) + (count >> 3);

			/* If the queue has receded below the threshold, we hold
			 * on to the last drain rate calculated, else we reset
			 * dq_count to 0 to re-enter the if block when the next
			 * packet is dequeued
			 */
			if (qlen < QUEUE_THRESHOLD) {
				flow->vars.dq_count = DQCOUNT_INVALID;
			} else {
				flow->vars.dq_count = 0;
				flow->vars.dq_tstamp = psched_get_time();
			}

			if (flow->vars.burst_time > 0) {
				if (flow->vars.burst_time > dtime)
					flow->vars.burst_time -= dtime;
				else
					flow->vars.burst_time = 0;
			}
		}
	}
}

static struct sk_buff *fq_pie_qdisc_dequeue(struct Qdisc *sch)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	struct sk_buff *skb = NULL;
	struct fq_pie_flow *flow;
	struct list_head *head;
	u32 uninitialized_var(pkt_len);

begin:
	head = &q->new_flows;
	if (list_empty(head)) {
		head = &q->old_flows;
		if (list_empty(head))
			return NULL;
	}

	flow = list_first_entry(head, struct fq_pie_flow, flowchain);
	if (flow->deficit <= 0) {
		flow->deficit += q->quantum;
		list_move_tail(&flow->flowchain, &q->old_flows);
		goto begin;
	}

	if (flow->head) {
		skb = dequeue_head(flow);
		pkt_len = qdisc_pkt_len(skb);
		sch->qstats.backlog -= pkt_len;
		sch->q.qlen--;
		qdisc_bstats_update(sch, skb);
	}

	if (!skb) {
		if (head == &q->new_flows && !list_empty(&q->old_flows))
			list_move_tail(&flow->flowchain, &q->old_flows);
		else
			list_del_init(&flow->flowchain);
		goto begin;
	}

	flow->qlen--;
	flow->deficit -= pkt_len;
	flow->backlog -= pkt_len;
	pie_process_dequeue(sch, skb, flow);
	return skb;
}

static void calculate_probability(struct Qdisc *sch, struct fq_pie_flow *flow)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	u32 qlen = sch->qstats.backlog;	/* queue size in bytes */
	psched_time_t qdelay = 0;	/* in pschedtime */
	psched_time_t qdelay_old = flow->vars.qdelay;	/* in pschedtime */
	s64 delta = 0;		/* determines the change in probability */
	u64 oldprob;
	u64 alpha, beta;
	u32 power;
	bool update_prob = true;

	flow->vars.qdelay_old = flow->vars.qdelay;

	if (flow->vars.avg_dq_rate > 0)
		qdelay = (qlen << PIE_SCALE) / flow->vars.avg_dq_rate;
	else
		qdelay = 0;

	/* If qdelay is zero and qlen is not, it means qlen is very small, less
	 * than dequeue_rate, so we do not update probabilty in this round
	 */
	if (qdelay == 0 && qlen != 0)
		update_prob = false;

	/* In the algorithm, alpha and beta are between 0 and 2 with typical
	 * value for alpha as 0.125. In this implementation, we use values 0-32
	 * passed from user space to represent this. Also, alpha and beta have
	 * unit of HZ and need to be scaled before they can used to update
	 * probability. alpha/beta are updated locally below by scaling down
	 * by 16 to come to 0-2 range.
	 */
	alpha = ((u64)q->params.alpha * (MAX_PROB / PSCHED_TICKS_PER_SEC)) >> 4;
	beta = ((u64)q->params.beta * (MAX_PROB / PSCHED_TICKS_PER_SEC)) >> 4;

	/* We scale alpha and beta differently depending on how heavy the
	 * congestion is. Please see RFC 8033 for details.
	 */
	if (flow->vars.prob < MAX_PROB / 10) {
		alpha >>= 1;
		beta >>= 1;

		power = 100;
		while (flow->vars.prob < div_u64(MAX_PROB, power) &&
		       power <= 1000000) {
			alpha >>= 2;
			beta >>= 2;
			power *= 10;
		}
	}

	/* alpha and beta should be between 0 and 32, in multiples of 1/16 */
	delta += alpha * (u64)(qdelay - q->params.target);
	delta += beta * (u64)(qdelay - qdelay_old);

	oldprob = flow->vars.prob;

	/* to ensure we increase probability in steps of no more than 2% */
	if (delta > (s64)(MAX_PROB / (100 / 2)) &&
	    flow->vars.prob >= MAX_PROB / 10)
		delta = (MAX_PROB / 100) * 2;

	/* Non-linear drop:
	 * Tune drop probability to increase quickly for high delays(>= 250ms)
	 * 250ms is derived through experiments and provides error protection
	 */

	if (qdelay > (PSCHED_NS2TICKS(250 * NSEC_PER_MSEC)))
		delta += MAX_PROB / (100 / 2);

	flow->vars.prob += delta;

	if (delta > 0) {
		/* prevent overflow */
		if (flow->vars.prob < oldprob) {
			flow->vars.prob = MAX_PROB;
			/* Prevent normalization error. If probability is at
			 * maximum value already, we normalize it here, and
			 * skip the check to do a non-linear drop in the next
			 * section.
			 */
			update_prob = false;
		}
	} else {
		/* prevent underflow */
		if (flow->vars.prob > oldprob)
			flow->vars.prob = 0;
	}

	/* Non-linear drop in probability: Reduce drop probability quickly if
	 * delay is 0 for 2 consecutive Tupdate periods.
	 */

	if (qdelay == 0 && qdelay_old == 0 && update_prob)
		/* Reduce drop probability to 98.4% */
		flow->vars.prob -= flow->vars.prob / 64u;

	flow->vars.qdelay = qdelay;
	flow->vars.qlen_old = qlen;

	/* We restart the measurement cycle if the following conditions are met
	 * 1. If the delay has been low for 2 consecutive Tupdate periods
	 * 2. Calculated drop probability is zero
	 * 3. We have atleast one estimate for the avg_dq_rate ie.,
	 *    is a non-zero value
	 */
	if ((flow->vars.qdelay < q->params.target / 2) &&
	    (flow->vars.qdelay_old < q->params.target / 2) &&
	    flow->vars.prob == 0 &&
	    flow->vars.avg_dq_rate > 0)
		pie_vars_init(&flow->vars);
}

static void fq_pie_timer(struct timer_list *t)
{
	struct fq_pie_sched_data *q = from_timer(q, t, adapt_timer);
	struct Qdisc *sch = q->sch;
	spinlock_t *root_lock = qdisc_lock(qdisc_root_sleeping(sch));
	int i;

	spin_lock(root_lock);

	for (i = 0; i < q->params.flows_cnt; i++)
		calculate_probability(sch, &q->flows[i]);

	// reset the timer to fire after 'tupdate'. tupdate is in jiffies.
	if (q->params.tupdate)
		mod_timer(&q->adapt_timer, jiffies + q->params.tupdate);
	spin_unlock(root_lock);
}

static const struct nla_policy fq_pie_policy[TCA_FQ_PIE_MAX + 1] = {
	[TCA_FQ_PIE_TARGET] = {.type = NLA_U32},
	[TCA_FQ_PIE_LIMIT] = {.type = NLA_U32},
	[TCA_FQ_PIE_TUPDATE] = {.type = NLA_U32},
	[TCA_FQ_PIE_ALPHA] = {.type = NLA_U32},
	[TCA_FQ_PIE_BETA] = {.type = NLA_U32},
	[TCA_FQ_PIE_ECN] = {.type = NLA_U32},
	[TCA_FQ_PIE_QUANTUM] = {.type = NLA_U32},
	[TCA_FQ_PIE_BYTEMODE] = {.type = NLA_U32},
	[TCA_FQ_PIE_FLOWS] = {.type = NLA_U32},
	[TCA_FQ_PIE_ECN_PROB] = {.type = NLA_U32}
};

static int fq_pie_change(struct Qdisc *sch, struct nlattr *opt,
			 struct netlink_ext_ack *extack)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	struct nlattr *tb[TCA_FQ_PIE_MAX + 1];
	unsigned int len_dropped = 0;
	unsigned int num_dropped = 0;
	unsigned int qlen;
	int err;

	if (!opt)
		return -EINVAL;

	err = nla_parse_nested(tb, TCA_FQ_PIE_MAX, opt, fq_pie_policy, NULL);
	if (err < 0)
		return err;

	if (tb[TCA_FQ_PIE_FLOWS]) {
		if (q->flows)
			return -EINVAL;
		q->params.flows_cnt = nla_get_u32(tb[TCA_FQ_PIE_FLOWS]);
		if (!q->params.flows_cnt ||
		    q->params.flows_cnt > 65536)
			return -EINVAL;
	}

	sch_tree_lock(sch);

	/* convert from microseconds to pschedtime */
	if (tb[TCA_FQ_PIE_TARGET]) {
		/* target is in us */
		u32 target = nla_get_u32(tb[TCA_FQ_PIE_TARGET]);

		/* convert to pschedtime */
		q->params.target = PSCHED_NS2TICKS((u64)target * NSEC_PER_USEC);
	}

	/* tupdate is in jiffies */
	if (tb[TCA_FQ_PIE_TUPDATE])
		q->params.tupdate = usecs_to_jiffies(nla_get_u32(tb[TCA_FQ_PIE_TUPDATE]));

	if (tb[TCA_FQ_PIE_LIMIT]) {
		u32 limit = nla_get_u32(tb[TCA_FQ_PIE_LIMIT]);

		q->params.limit = limit;
		sch->limit = limit;
	}

	if (tb[TCA_FQ_PIE_ECN_PROB])
		q->params.ecn_prob = nla_get_u32(tb[TCA_FQ_PIE_ECN_PROB]);

	if (tb[TCA_FQ_PIE_ALPHA])
		q->params.alpha = nla_get_u32(tb[TCA_FQ_PIE_ALPHA]);

	if (tb[TCA_FQ_PIE_BETA])
		q->params.beta = nla_get_u32(tb[TCA_FQ_PIE_BETA]);

	if (tb[TCA_FQ_PIE_ECN])
		q->params.ecn = nla_get_u32(tb[TCA_FQ_PIE_ECN]);

	if (tb[TCA_FQ_PIE_QUANTUM])
		q->quantum = nla_get_u32(tb[TCA_FQ_PIE_QUANTUM]);

	if (tb[TCA_FQ_PIE_BYTEMODE])
		q->params.bytemode = nla_get_u32(tb[TCA_FQ_PIE_BYTEMODE]);

	/* Drop excess packets if new limit is lower */
	qlen = sch->q.qlen;
	while (sch->q.qlen > sch->limit) {
		struct sk_buff *skb = fq_pie_qdisc_dequeue(sch);

		kfree_skb(skb);
		len_dropped += qdisc_pkt_len(skb);
		num_dropped += 1;
	}
	qdisc_tree_reduce_backlog(sch, num_dropped, len_dropped);

	sch_tree_unlock(sch);
	return 0;
}

static int fq_pie_init(struct Qdisc *sch, struct nlattr *opt,
		       struct netlink_ext_ack *extack)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	int err;
	int i;

	fq_pie_params_init(&q->params);
	sch->limit = 10 * 1024;
	q->params.ecn_prob = 10;
	q->params.limit = sch->limit;
	q->params.flows_cnt = 1024;
	q->quantum = psched_mtu(qdisc_dev(sch));
	q->sch = sch;

	INIT_LIST_HEAD(&q->new_flows);
	INIT_LIST_HEAD(&q->old_flows);

	timer_setup(&q->adapt_timer, fq_pie_timer, 0);
	mod_timer(&q->adapt_timer, jiffies + HZ / 2);

	if (opt) {
		int err = fq_pie_change(sch, opt, extack);

		if (err)
			return err;
	}

	if (!q->flows) {
		q->flows = kvcalloc(q->params.flows_cnt,
				    sizeof(struct fq_pie_flow),
				    GFP_KERNEL);
		if (!q->flows) {
			err = -ENOMEM;
			goto init_failure;
		}
		for (i = 0; i < q->params.flows_cnt; i++) {
			struct fq_pie_flow *flow = q->flows + i;

			INIT_LIST_HEAD(&flow->flowchain);
			pie_vars_init(&flow->vars);
		}
	}
	return 0;

init_failure:
	q->params.flows_cnt = 0;

	return err;
}

static int fq_pie_dump(struct Qdisc *sch, struct sk_buff *skb)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	struct nlattr *opts;

	opts = nla_nest_start(skb, TCA_OPTIONS);
	if (!opts)
		goto nla_put_failure;

	/* convert target from pschedtime to us */
	if (nla_put_u32(skb, TCA_FQ_PIE_TARGET,
		((u32)PSCHED_TICKS2NS(q->params.target)) /
		NSEC_PER_USEC) ||
		nla_put_u32(skb, TCA_FQ_PIE_LIMIT, sch->limit) ||
		nla_put_u32(skb, TCA_FQ_PIE_TUPDATE, jiffies_to_usecs(q->params.tupdate)) ||
		nla_put_u32(skb, TCA_FQ_PIE_ALPHA, q->params.alpha) ||
		nla_put_u32(skb, TCA_FQ_PIE_BETA, q->params.beta) ||
		nla_put_u32(skb, TCA_FQ_PIE_ECN, q->params.ecn) ||
		nla_put_u32(skb, TCA_FQ_PIE_BYTEMODE, q->params.bytemode) ||
		nla_put_u32(skb, TCA_FQ_PIE_QUANTUM, q->quantum) ||
		nla_put_u32(skb, TCA_FQ_PIE_FLOWS, q->params.flows_cnt) ||
		nla_put_u32(skb, TCA_FQ_PIE_ECN_PROB, q->params.ecn_prob))
		goto nla_put_failure;

	return nla_nest_end(skb, opts);

nla_put_failure:
	return -1;
}

static int fq_pie_dump_stats(struct Qdisc *sch, struct gnet_dump *d)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);
	struct tc_fq_pie_xstats st = {
		.packets_in	= q->stats.packets_in,
		.overlimit	= q->stats.overlimit,
		.dropped	= q->stats.dropped,
		.ecn_mark	= q->stats.ecn_mark,
		.new_flow_count = q->stats.new_flow_count,
	};
	struct list_head *pos;

	sch_tree_lock(sch);
	list_for_each(pos, &q->new_flows)
		st.new_flows_len++;

	list_for_each(pos, &q->old_flows)
		st.old_flows_len++;
	sch_tree_unlock(sch);

	return gnet_stats_copy_app(d, &st, sizeof(st));
}

static void fq_pie_destroy(struct Qdisc *sch)
{
	struct fq_pie_sched_data *q = qdisc_priv(sch);

	kvfree(q->flows);
	del_timer_sync(&q->adapt_timer);
}

static struct Qdisc_ops fq_pie_qdisc_ops __read_mostly = {
	.id = "fq_pie",
	.priv_size	= sizeof(struct fq_pie_sched_data),
	.enqueue	= fq_pie_qdisc_enqueue,
	.dequeue	= fq_pie_qdisc_dequeue,
	.peek		= qdisc_peek_dequeued,
	.init		= fq_pie_init,
	.destroy	= fq_pie_destroy,
	.change		= fq_pie_change,
	.dump		= fq_pie_dump,
	.dump_stats	= fq_pie_dump_stats,
	.owner		= THIS_MODULE,
};

static int __init fq_pie_module_init(void)
{
	return register_qdisc(&fq_pie_qdisc_ops);
}

static void __exit fq_pie_module_exit(void)
{
	unregister_qdisc(&fq_pie_qdisc_ops);
}

module_init(fq_pie_module_init);
module_exit(fq_pie_module_exit);

MODULE_DESCRIPTION("Flow Queue Proportional Integral controller Enhanced (FQ-PIE) scheduler");
MODULE_AUTHOR("Gautam Ramakrishnan");
MODULE_AUTHOR("V Saicharan");
MODULE_AUTHOR("Mohit Bhasi");
MODULE_AUTHOR("Leslie Monis");
MODULE_LICENSE("GPL");
