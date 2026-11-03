# Affineness of actual homogeneous quotients by field descent

This is a derived internal adapter for the existing actual homogeneous quotient,
its arbitrary base change, the effective-epimorphism comparison construction,
and `Langlands.AlgebraicGeometry.fieldExtensionAffineDescent`. Worker 362
authored this pair. There is no additional source assertion or geometric
existence hypothesis implicit in this derivation.

For two `HomogeneousQuotient i` bundles over the same arbitrary scheme,
`comparisonIso` constructs an isomorphism over the base between their actual
quotient schemes. Both projections are smooth, surjective and quasi-compact,
so their underlying scheme maps are effective epimorphisms. Each bundle
identifies equality of projected points on every relative scheme test with
membership of the right difference in the range of the same subgroup map.
Their fibers therefore agree, and `HomogeneousQuotientComparison.iso` applies.
`projection_comparisonIso_hom` records compatibility with the projections.

`isAffine_of_comparison` transfers affineness of the target quotient model
along this actual scheme isomorphism.

For fields `k` and `K` in any common universe, with any `k`-algebra structure
on `K`, `isAffine_of_fieldExtension` takes an actual quotient `D` over `k`
and an affine actual quotient `E` of the base-changed subgroup inclusion over
`K`. It does not assume the two supplied models are definitionally equal.
First, `D.baseChange` has the same exact all-test coset fibers as `E`, so
comparison makes its underlying scheme affine. That underlying scheme is the
literal pullback of `D.scheme.hom` along the spectrum of `algebraMap k K`.
The published field-extension affineness theorem then proves that the original
scheme of `D` is affine.

No algebraic closure, unipotence, normality, action, or dimension hypothesis is
needed for this transfer. This adapter does not assert existence of either
supplied homogeneous quotient or discharge an affine model's hypotheses.
