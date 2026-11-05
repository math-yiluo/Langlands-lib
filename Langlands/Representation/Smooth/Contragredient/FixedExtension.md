# Smooth functional extension at the given compact open level

This internal construction supplies the precise fixed-level dual extension
needed when a smooth representation is embedded in another smooth
representation. Its mathematical inputs are the published
`smoothDualFixedRestriction_bijective` and Mathlib's linear left-inverse
construction. It is a direct derived adapter of these results, with no new
source assertion. It refines the useful conclusion of the published smooth
contragredient exactness theorem by retaining the given compact open subgroup.

Let G be a topological group, let ρ and σ be smooth complex representations on
V and W, and let K be the specified compact open subgroup. The group and the
two module carriers have independent universes `uG`, `uV` and `uW`. There is no
admissibility or finite-dimensionality hypothesis. The modules carry no
topology. A smooth dual vector is an element of the existing smooth part of
the full algebraic dual, with the existing contragredient action.

`smoothDualCompactFixedEquiv` bundles the published compact-open restriction
bijection as a complex linear equivalence between the K-fixed smooth dual and
the algebraic dual of the K-fixed original vectors.

For an intertwiner f from ρ to σ, `smoothDualFixedExtension` first restricts a
K-fixed smooth functional on V to the K-fixed vectors. It composes the
resulting functional with Mathlib's chosen linear left inverse of
`fixedVectorsMap f K.toSubgroup`, obtaining a functional on the K-fixed vectors
of W. The inverse of the target compact-open duality equivalence gives a
K-fixed smooth functional on W. This is a complex linear map between the
fixed smooth dual spaces. Mathlib's chosen left inverse is defined for any
linear map, with value zero when that map is not injective; the extension
conclusions below require injectivity of f.

`smoothDualFixedExtension_restrict` gives the construction's exact restriction
formula. If f is injective, its map on K-fixed vectors is injective.
`smoothDualFixedExtension_pullback` proves that pulling the extended
functional back along f recovers the original functional. The proof compares
their restrictions using injectivity of the published compact-open duality
map, then evaluates the linear left-inverse identity at every fixed vector.
`fixedVectorsMap_contragredient_surjective_of_injective` records the resulting
surjectivity at this exact subgroup K.

`smoothDualFixedExtension_apply` evaluates that identity at every vector of V,
including vectors that are not K-fixed. Finally,
`smoothDualFixedExtension_inverseCoefficient` uses equivariance of f at g⁻¹
to identify the actual inverse coefficient of the extended functional and
embedded vector with the original inverse coefficient at every element g.
The same functional, vector, group element and fixed subgroup occur in these
equalities.

This construction can be applied to a norm-kernel representation once an
injective intertwiner into a restricted ambient smooth representation is
available. The published actual-inclusion and smooth-dual comparison modules
then compare that restricted action with the ambient one. Existence of such
an ambient representation and embedding, the common compact support bound,
its compactness on the actual kernel, fixed-level class finiteness and category
decomposition remain separate mathematical obligations.

The module imports published compact-open fixed duality and its construction,
and the published fixed-functional restriction evaluation and naturality
module. It uses `LinearMap.leftInverse`, `LinearMap.leftInverse_apply_of_inj`
and `LinearMap.ker_eq_bot` from Mathlib. Worker 485 authored this adapter using
those imported results; no shared draft is incorporated.
