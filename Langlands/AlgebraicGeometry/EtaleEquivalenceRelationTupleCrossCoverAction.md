# The higher-tail action on a tuple cross cover

This is derived internal scheme infrastructure for the symmetric tuple
filtration of Stacks Project, Lemmas 68.8.3 (Tag 0BBN) and 68.8.6 (Tag
07ST), registered as `stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. It uses the previously
constructed tuple presentations and their actual chart comparison.
All constructions work in arbitrary universe `u`. They assume a
separated source for the original relation, affine object and arrow
schemes, and a closed joint endpoint map.

For `p ≤ q`, write `L` for the tail beginning at `p` and `H` for the
tail beginning at `q`. The cross cover is the pullback of the source
of `L` along the inclusion of the objects of `H`. Its maps are the
chosen higher source, its original lower arrow, and its lower target.

`tupleTailToTailRelationMap` is the reindexing map on arrows. Its
`_t` and `_s` equations identify both endpoint composites.
`tupleTailToTailChartIso_hom_t` and `_hom_s` record the corresponding
endpoint equations for the chart comparison isomorphism.

`tupleTailCrossCover_hom_ext` says that the higher source and lower
target determine a morphism into the cross cover. Pullback extensionality
reduces this to endpoint extensionality in the lower relation.

`tupleTailCrossCoverActionMap` constructs the action. If `a` is a
higher-tail arrow and `b` a cross arrow with matching sources, compose
the lower arrow of `b` with the inverse of the image of `a`. Its new
source lifts to the target of `a`, so this defines a cross-cover map.
`_source` identifies its higher source and `_target` proves that its
lower target is preserved.

`tupleTailCrossCoverAction` packages the map as an actual action.
Both unit and associativity follow from cross-cover extensionality:
the target is preserved, and the source follows the target of the
acting arrow. `tupleTailCrossCoverAction_target` restates target
invariance for the packaged action. When `q < N+1`,
`tupleTailCrossCoverAction_threshold` proves invariance of the
surjective etale threshold cover by cancelling the threshold open
inclusion.

This construction is pullback and equivalence relation algebra for the
established tuple charts. It makes no Noetherian approximation claim.
