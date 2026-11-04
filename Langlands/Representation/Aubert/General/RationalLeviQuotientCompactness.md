# Compact quotient representatives inside actual standard Levis

This internal construction specializes
[SemidirectQuotientCompactness](SemidirectQuotientCompactness.md) to the
actual standard rational-point families. It uses the canonical evaluation
topology `pointTopology` over an arbitrary nonarchimedean local field. It
retains local compactness and the nonarchimedean group instance, the standard
cocharacter and Levi-intersection statements, connected reductivity, a maximal
split torus, and a generic cocharacter.

For `K : Finset (SimpleRoot i ν)` and `I : Finset K`, the definition
`standardLeviCompactCosetCover` returns an actual compact subset of `M_K`
and a certificate that each `m : M_K` has the form `q * c`, where
`q` belongs to the literal subgroup
`(P_(leviIndex K I)).subgroupOf M_K` and `c` belongs to that compact subset.
Its additional premise is compactness of the ambient quotient
`P_(leviIndex K I) \ G`.

The implemented construction uses the standard decomposition
`P_K = M_K ⋉ U_K`. The published
`standardParabolic_isClosed_of_standardCocharacterStatement` and
`continuous_standard_projection` give closedness of `P_K` and continuity of
its actual Levi projection. The published standard subgroup monotonicity
theorems give
`U_K ≤ P_(leviIndex K I) ≤ P_K`.
The generic semidirect construction intersects ambient compact coset
representatives with the closed `P_K` and projects them into `M_K`.
It proves that the projected compact set covers the required inside-Levi
quotient. Classical choice exposes this set and its two certificates.

`compactSpace_leftQuotient_in_levi_of_ambient` applies the existing compact
coset-cover criterion to that returned set. Its quotient is exactly
`Induction.LeftQuotient ((P_(leviIndex K I)).subgroupOf M_K)`, with the quotient
topology induced from the subgroup topology on `M_K`.

`compactSpace_leftQuotient_in_levi_of_dynamic` obtains the ambient compactness
premise from the published adapter `compactSpace_leftQuotient_parabolic` in
[RationalInductionDualityReduction](RationalInductionDualityReduction.md).
It retains `BruhatTits.DynamicParabolicQuotientCompactStatement` as an explicit
premise. This module proves neither that uniform statement nor the full
`RationalSupportCategoryJacquetVanishingStatement`.

The construction has no representation carrier, root finiteness, endpoint,
finite-length, or admissibility premise. It includes empty finite subsets and
rank zero. Its provenance is an internal specialization of the cited published
constructions; it introduces no new external source assertion.
