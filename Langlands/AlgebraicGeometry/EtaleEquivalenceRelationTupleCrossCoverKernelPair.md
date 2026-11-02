# The kernel pair of the affine tuple threshold cover

This is derived scheme infrastructure for the symmetric tuple
filtration in Stacks Project, Lemmas 68.8.3 (Tag 0BBN) and 68.8.6
(Tag 07ST), registered as `stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. It uses the previously
constructed action and actual chart comparison, without an
approximation assumption.

All declarations work in arbitrary scheme universe `u`, with separated
source, affine object and arrow schemes, and a closed joint endpoint
map for the original relation. For `p ≤ q`, the lower relation is the
finite tuple tail beginning at `p`, and the higher relation begins at
`q`. The cross cover is the pullback of the lower source along the
higher object inclusion.

`tupleTailToTailChartIso_inv_t` and `_inv_s` identify the endpoint
composites of the inverse chart comparison. They follow from the
forward equations and the inverse isomorphism law.

`tupleTailCrossCoverComparisonArrow` takes two cross arrows with equal
lower targets. Reverse the first lower arrow and compose it with the
second. Its endpoints have the two chosen higher lifts, so the chart
comparison gives an actual higher-tail arrow from the second lift to
the first. The equations `_t` and `_s` record those endpoints using
the chart lifting equations.

`tupleTailCrossCoverAction_target_isPullback` identifies the action
relation square with the kernel pair of the lower target map.
Uniqueness is endpoint extensionality in the action relation. For
existence, pair the comparison arrow with the second cross arrow.
Its action equals the first cross arrow: cross-cover extensionality
reduces this to target invariance and the comparison arrow's target.

Under `q < N+1`, `tupleTailCrossCoverAction_threshold_isPullback`
gives the same result for the surjective etale threshold cover.
Equality over the threshold implies equality of lower targets by
composition with the open inclusion, so the preceding pullback
construction supplies each lift.

`tupleTailCrossCoverKernelPairIso` is the resulting actual isomorphism
from the action relation's arrow scheme to the scheme pullback of
the threshold cover with itself. The equations `_hom_fst` and
`_hom_snd` identify the two projections with action target and source,
respectively. The equations `_inv_t` and `_inv_s` give the inverse
projection identities. These are the standard projection identities
for the isomorphism from a limiting pullback square to the chosen
pullback.

The comparison is internal pullback and equivalence relation algebra
on the established tuple charts; it asserts no Noetherian model.
