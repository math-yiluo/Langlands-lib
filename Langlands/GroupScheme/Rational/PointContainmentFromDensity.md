# Closed subgroup containment from dense rational points

Worker 1754 prepared this internal helper as support for the structural
prerequisite of represented-parabolic transitivity. It does not prove the nested-radical decompositions.

`SubgroupFunctor.range_le_of_dense_rationalPoints` works over an arbitrary
field of arbitrary universe. Its source group scheme has a reduced underlying
scheme and Zariski dense actual rational points; its target subgroup map is
a closed immersion. Inclusion of the two images on ground-field points then
implies inclusion of their range subgroup functors on every test scheme.
There is no injectivity assumption on the source homomorphism, nor any
finite-type, reducedness or separatedness assumption on the target.

The proof generalizes the published internal helper
`SubgroupFunctor.range_le_of_algClosed_points` from
`Langlands.GroupScheme.Absolute.RationalSubgroupContainment`. Pull back the
closed subgroup inclusion along the source map. Each rational point factors
through this pullback by the point-image hypothesis. Its projection therefore
has dense image. Its image is closed, so it is surjective; a surjective closed
immersion into a reduced scheme is an isomorphism. Its inverse gives the
underlying factorization, hence inclusion on every test scheme.

`SubgroupFunctor.range_le_of_localField_points` applies this to a smooth
connected affine source over an actual nonarchimedean local field, using
the published `hasDenseRationalPoints_of_localField`. Smoothness supplies
reducedness. The topology is on the field only; no topology on the group
of points is needed.

The provenance is derived from the indicated published helper and density
theorem and Mathlib's pullback, closed-immersion and reduced-scheme facts.
No new literature claim or geometric structure theorem is used here.
