# Integer-line Moeglin–Waldspurger algorithm

Worker 963. This module implements the algorithm in Moeglin–Waldspurger,
*Sur l'involution de Zelevinski* (1986), II.1–II.2, printed pp.148–149,
in the equivalent shortest-segment form of Badulescu,
*On p-adic Speh representations* (2014), paragraph “The algorithm”,
retained `1110.5080.tex`, lines 107–134.

`Interval` records endpoints `beginning ≤ ending`. Its length includes both
endpoints. `Multisegment` is a genuine finite multiset, and its support is a
multiset of integer points. Beginnings and endings also retain multiplicity.
The empty input is included.

Descending order first maximizes the ending and then the beginning; at a fixed
ending, this is exactly the shortest segment. `pick` restricts a subsequent
selection to ending `e` and beginning strictly below the previous beginning.
Since the previous ending is `e+1`, this is precisely noncontainment in the
previous interval. `chain` erases one occurrence at each selection and proceeds
to ending `e-1`. It returns an ordered list together with the untouched
multiset. `Round.selectedList` retains this order, while `Round.selected` is
its multiset of occurrences. Equal intervals are indistinguishable choices but remain
separate occurrences in the multiset.

`round` chooses the first interval by canonical sorting. It emits `[e-r,e]`
when there are `r+1` selections. Its residual is the untouched multiset plus
the right truncations of exactly the selected occurrences; singleton
truncations are discarded. `dual` recurses on this residual. The inner
recursion decreases multiset cardinality. The intrinsic partition and
shortening lemmas prove that the outer recursion strictly decreases `weight`,
the sum of lengths. There is no fuel cutoff or mathematical correctness
assumption. The empty input has empty output, and `dual_of_round` is the
recursive equation.

These are definitions and intrinsic implementation lemmas. Support preservation,
involutivity, output-length bounds and representation-theoretic correctness
are separate, unproved proposition targets.

`chain_partition` and `round_partition` prove the exact multiset decomposition
into selected and untouched occurrences by well-founded induction and
`Multiset.cons_erase`. `chain_beginnings_lt`, `chain_decreasing` and
`round_decreasing` prove strict descent of the selected beginnings;
`chain_ending` and `round_ending` give the consecutive endings by list index.
These are intrinsic facts of the selection procedure, proved by unfolding one
recursive call and applying the induction hypothesis. They do not assume any
property of the completed dual multisegment. The ordering, raw round structure
and termination lemmas are implementation choices derived from the cited
algorithm. Extending the domain to the empty input makes the recursion total.
