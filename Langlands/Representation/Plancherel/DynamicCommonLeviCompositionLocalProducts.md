# Compact-open products for common-Levi composition

Worker 360, supporting Task 7002.

This internal helper proves the three local compact-open product identities used by
`StandardIntertwining.DynamicSource.comp_hasIntegral` for three actual dynamic radicals.
It imports the published target module without changing it. It takes an arbitrary
`OrderedSubgroupFactorization` with complements `V = U₁ ∩ Ū₀` and `W = U₂ ∩ Ū₁`;
it neither constructs that factorization nor assumes its structural target as an axiom.
The two complement closedness lemmas are intersections of the published closed radicals.

The provenance is the measure-normalization step of the Library's conditional form
of Waldspurger 2003, IV.1 (12), described in the paired
`DynamicCommonLeviComposition.md`. The present local identities are internal
consequences of `CommonLeviSplitting.SplitsAlong` and the supplied factorization,
with proofs modeled on the published `StandardIntertwiningOppositeCharts` lemmas.
They make no new claim about root distances or the existence of a suitable compact open.

For the first product, `SplitsAlong.second` reverses the splitting order by inversion,
giving `Q ∩ U₁ = (Q ∩ U₀ ∩ U₁)(Q ∩ V)` after commuting the two subgroups in the
description of `V`. Membership in each source compact open is literally membership
in `Q` after forgetting subtype wrappers. The proof writes the two factors as elements
of the actual subgroup carriers and uses `firstSubgroupProduct_eq` to identify their
product. The second product repeats this argument with indices shifted by one.

For the middle product, start with `x ∈ Q ∩ U₁ ∩ U₂` and write `x = a b` using the
first splitting. The factorization supplies `V ≤ U₂`, so `b ∈ U₂` and
`a = x b⁻¹ ∈ U₂`. Consequently `a ∈ Q ∩ U₀ ∩ U₂` and `b ∈ Q ∩ V`, as required by
the two nested carriers in `intersectionSubgroupProduct`. The forward inclusions of
all three product identities use closure of the corresponding compact open under
multiplication.

No reductivity, common-Levi equality, splitness, quasisplitness or characteristic
restriction is added by these helpers. The ambient hypotheses are those used by the
published dynamic objects. The proof uses only standard Lean axioms.
