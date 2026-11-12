# Split rank one for a supplied quaternionic spin cover

This internal consequence of the published rank comparison and central-isogeny
rank transport belongs to Task 5397. It uses the actual `IsSpinCover` predicate
and the published quotient-valued quadratic forms.

`SpinCoverWittIndexOneStatement` quantifies over every infinite field `K` in
arbitrary universe `u`, every finite-dimensional division `K`-algebra `D` with a
first-kind involution, and every nondegenerate quadratic form of quadratic Witt
index one. Every supplied spin cover is simply connected and has split rank one.
No restriction on characteristic, the dimension of `D`, or the number of
variables is added. In particular, the statement applies to the covers in
`LocalSpinRankOneStatement` after obtaining infinitude from the local-field
hypotheses.

The theorem `IsSpinCover.splitRank_eq_one` installs the smoothness of the actual
isometry group recorded by the supplied cover. The published
`FirstKindInvolution.splitRank_connectedIsometryGroup_eq_one` then computes the
rank of its identity component, and `IsSpinCover.splitRank_eq` transfers that
rank to the cover through its central isogeny. The theorem
`spinCoverWittIndexOne` pairs this conclusion with the simple connectedness
already included in `IsSpinCover`.

This is a composition of published results and makes no new literature claim.
It proves the rank assertion for a supplied cover. Existence of a cover and its
almost simplicity still require the geometric input to the full local theorem.
