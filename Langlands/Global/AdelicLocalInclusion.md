# Local factors inside actual adelic group points

For an arbitrary number field `F : Type u` and an affine group scheme `G` over
`F`, `AdelicGroupPoints.ofPlace F G i` inserts an actual point over the completion
at `i` and the identity at every other place. It is a group homomorphism into the
existing `AdelicGroupPoints F G`, constructed with `glue`. No change of point
carrier or topology is made.

The coordinate formulas identify its projection at `i` with its input and its
other projections with the identity. Continuity is checked on every regular
function: the archimedean coordinates are continuous, while the finite coordinates
factor through a restricted product with one fixed cofinite integral tail. The
tail comes from the regular-function value at the identity, omitting the inserted
place as well. Thus the dependence on the input occurs in at most one local
coordinate. `ofPlaceContinuous` bundles the same map as a continuous homomorphism.

The continuous projection at `i` is a left inverse. Hausdorffness therefore makes
the insertion a closed embedding. Its range consists exactly of points whose
other local projections are the identity; this also proves normality. Insertions
at distinct places commute, as is checked on every local projection. No local
finite-type, smoothness, connectedness or reductivity assumption is needed.

This is internal infrastructure derived from the existing local projections,
almost-everywhere integrality, gluing and regular-function evaluation topology in
`AdelicGroupLocalPoints`. It does not assert a Haar-measure or modular-character
comparison.
