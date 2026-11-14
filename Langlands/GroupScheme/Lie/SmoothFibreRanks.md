# Lie ranks of smooth affine groups at field-valued points

`SmoothFibreRankStatement` states the field-valued rank comparison and
`smoothFibreRank` proves it. These internal consequences of published Library results relate the actual
relative dual-number Lie module of a smooth affine group over an arbitrary
commutative ring to the Lie dimension of its field-valued fibres.

`finrank_lieKernel_eq_rankAtStalk` combines the published scalar-extension
equivalence for smooth affine Lie modules with Mathlib's rank base-change
formula. `dimension_baseChange_eq_rankAtStalk` additionally uses the actual
scheme-pullback comparison of Lie kernels. Finite projectivity gives local
constancy of this rank.

`isIso_of_mono_of_dimension_eq` applies over a field. The published image
theorem makes a monic homomorphism from a smooth connected affine group a
closed immersion. Its differential is injective, and equal Lie dimensions
make it surjective. The published full-Lie subgroup criterion then makes the
homomorphism an isomorphism. Both groups are smooth, connected and affine.

The provenance is internal; no new source assertion or base regularity
assumption is used.
