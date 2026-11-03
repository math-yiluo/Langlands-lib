# Closed split-torus lifts from split-torus parametrizations

Author: Worker 1437.

This internal helper is a consequence of the published dominant split-torus
image construction and descent of containment through a schematically dominant
map. It is intended for the split maximal-torus lift proof. It does not construct
a parametrization or prove the unconditional lifting statement.

`SplitParametrizationLiftStatement.{u}` defines the internal interface, and
`splitParametrizationLiftStatement` proves it using the more conveniently
implicit-parameter helper
`exists_splitSubtorus_lift_of_surjective_splitParametrization`.

Let `π : G → H` be any group-scheme homomorphism over an arbitrary field, with
`G` affine. Suppose that `D` is split, `i : S → H` is a closed subgroup, and
`a : D → G` and `b : D → S` satisfy `a ≫ π = b ≫ i`, with the underlying
scheme map of `b` surjective. The helper returns a closed split subtorus
`j : T → G` and an actual commutative-group-scheme homomorphism `f : T → S`.
The underlying scheme map of `f` is surjective, and `j ≫ π = f ≫ i`.
The argument does not require splitness or even torus structure on `S`.

Take the dominant closed split image `D → T → G` of `a`. The composite
`T → G → H` lands in the closed subgroup `S` because its precomposition
with the schematically dominant map `D → T` does. The represented-subgroup
factorization gives `f`. The two maps from `D` to `S` agree after the closed
inclusion `i`, so they agree. Thus the surjective map `b` is the composite
`D → T → S`, which makes `f` surjective on the underlying schemes.

The Lean proof uses `IsSplitTorus.dominantFactorization`,
`SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant`,
`SubgroupFunctor.IsRepresentedBy.factorHom` and its uniqueness through the
closed inclusion, and Mathlib's `Surjective.of_comp`. Every field and universe
is retained. Finiteness, flatness, centrality, and maximality are unnecessary
for this intermediate result; the main proof must establish its input
parametrization and use a separate maximality argument.
