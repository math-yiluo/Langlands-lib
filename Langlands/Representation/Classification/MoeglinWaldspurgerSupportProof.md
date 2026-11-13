# Support preservation for the Moeglin–Waldspurger recursion

Worker 963.

`Langlands.MoeglinWaldspurger.supportPreservation` proves exactly the published
proposition `SupportPreservation`: for every finite integer multisegment `a`,
the multiset `support (dual a)` equals `support a`. Multiplicities and the
empty input are included.

This is an internal proof about the published integer-interval algorithm.
Its source convention is Badulescu, *On p-adic Speh representations* (2014),
retained `1110.5080.tex`, lines 116–136, describing the algorithm of
Moeglin–Waldspurger, *Sur l'involution de Zelevinski* (1986), II.1–II.2,
printed pp.148–149. The new bookkeeping lemmas are derived from the
implementation rather than separate assertions quoted from the literature.

The implemented proof first shows that shortening one nonempty interval
removes precisely its ending, with singleton intervals disappearing. Multiset
induction then proves that shortening a selected multisegment removes exactly
its multiset of endings. A list induction identifies a consecutive descending
list of endings with the support of the emitted interval, whose support is
enumerated in ascending order. The published `round_ending` lemma supplies
that consecutiveness. Combining this identity with `round_partition` gives
the support partition for one complete round.

Finally, well-founded induction on the published total weight applies
`dual_of_round` and the induction hypothesis at `round_weight_lt`. The
one-round support partition gives the result. When no round exists,
`round_none_iff` reduces the input to the empty multisegment and `dual_zero`
finishes. All comparisons are multiset equalities, so repeated intervals and
repeated points retain their full multiplicities.
