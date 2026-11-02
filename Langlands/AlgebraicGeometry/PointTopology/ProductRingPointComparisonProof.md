# Proof of the relative product-ring point comparison

`productRingPointComparison` proves the published
`ProductRingPointComparisonStatement` for actual morphisms over `Spec C`.
The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(31 December 2011), formula (3.6.2) and its proof, printed pages 7–8,
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The proof reuses the pinned Mathlib module `Mathlib.AlgebraicGeometry.PointsPi`
by Andrew Yang. Its theorems `AlgebraicGeometry.pointsPi_injective`,
`AlgebraicGeometry.pointsPi_surjective_of_isAffine`, and
`AlgebraicGeometry.pointsPi_surjective` prove the corresponding assertions for
unrestricted scheme morphisms. The published map's exact underlying
identification with `pointsPi` is the host comparison used here.

For injectivity, equality of relative component points gives equality of their
underlying scheme morphisms. The Mathlib injectivity theorem, using only
`QuasiSeparatedSpace X.left`, gives equality of the underlying product points.
`RingPoint.ext` then gives equality in the slice category.

For both surjectivity clauses, first lift the family of underlying scheme
morphisms by the corresponding Mathlib theorem. The lift still needs to satisfy
the base equation. `productPointLift_base` proves that equation by applying
Mathlib injectivity to the target `Spec C`, which is affine and therefore
quasi-separated. On each factor, the equation follows from the given relative
point's base equation and the algebra compatibility of the coordinate projection.
This step places no quasi-separatedness assumption on `X`. Rebuilding the lift
as an actual slice morphism completes `productPointMap_surjective_of_underlying`.

The affine surjectivity lemma supplies Mathlib's affine lift without any local
factor assumption. The quasi-compact surjectivity lemma supplies Mathlib's lift
for local factors without any quasi-separatedness assumption on `X`. The final
theorem packages these lemmas and injectivity into the exact three-clause
statement. It introduces no assumed geometric conclusion or additional source
hypothesis.
