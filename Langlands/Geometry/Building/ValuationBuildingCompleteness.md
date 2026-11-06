# Completeness of a building metric with isometric apartment charts

This module proves Kaletha–Prasad (2023), Theorem 4.2.10 (first assertion:
the building is complete), printed pp.171–172 / PDF pp.202–203, for a metric on
the existing quotient `B.ReducedBuilding` of a `ValuationBuildingData` `B`. It
uses the orbit discreteness of Lemma 4.2.11 (second assertion), proved here
from the apartment `A(S)` by a route that differs from the source; see below.
The module does not construct a metric on `B(G)`. It also proves
two facts about the Euclidean root metric on `A(S)` from
`Langlands.Geometry.Building.ValuationApartmentMetric`.

## Declarations

All names are in the namespace `Langlands.Geometry.Building.ValuationBuildingData`.

| Lean name | Statement |
| --- | --- |
| `exists_normalizer_smul_eq_of_smul_apartmentMap_eq` | If `g • [a] = [b]` for apartment points `a, b` and `g ∈ G(F)`, then `n • a = b` for some `n ∈ N(F)` |
| `dist_smul_apartmentMap` | If the apartment map is an isometry and `G(F)` acts isometrically, then `dist (h • [a]) (h • [b]) = dist a b` |
| `dist_normalizer_smul` | Under the same hypotheses, `N(F)` acts isometrically on `A(S)` |
| `exists_forall_dist_smul_apartmentMap_lt_imp_eq` | Lemma 4.2.11, second assertion, at a point `[b]` of the base apartment: if every `n ∈ N(F)` with `dist (n • b) b < ε` fixes `b`, then every `g ∈ G(F)` with `dist (g • [b]) [b] < ε` fixes `[b]` |
| `exists_forall_dist_smul_lt_imp_eq` | Lemma 4.2.11, second assertion, at every point of `B(G)`, for the full group `G(F)` |
| `completeSpace_of_isometry_apartmentMap` | Theorem 4.2.10: for any metric on `A(S)` that is proper, if the apartment map is an isometry, `G(F)` acts isometrically, any two points share an apartment and `N(F)`-orbits in `A(S)` are discrete, then `B(G)` is complete |
| `apartment_properSpace` | The Euclidean root metric on `A(S)` is proper |
| `exists_forall_dist_normalizer_smul_lt_imp_eq` | Under `B.SatisfiesApartmentAxioms`, the `N(F)`-orbits in `A(S)` are discrete for the Euclidean root metric |
| `completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms` | Theorem 4.2.10 for a metric on `B(G)` that pulls back to the Euclidean root metric along the apartment map |

Here `[a]` denotes `B.apartmentMap a`. In the last three declarations the
metric on `A(S)` is the Euclidean root metric `apartmentMetricSpace` of
`ValuationApartmentMetric`, installed through local instances. The common-apartment
hypothesis is
`hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x`. The
metric on `B.ReducedBuilding` and `IsIsometricSMul (rationalPoints G)
B.ReducedBuilding` are instance arguments.

## Proofs as implemented

*The quotient relation.* `exists_normalizer_smul_eq_of_smul_apartmentMap_eq`
unfolds `g • [a] = [b]` to an equality of classes in the existing
`ApartmentQuotient` and reads off `n ∈ N(F)` with `n • a = b` from
`ApartmentQuotient.mk_eq_mk_iff`. This is the relation (7.6.2) that defines the
quotient (KP Remark 7.6.5). `dist_normalizer_smul` combines this with
`normalizer_smul_apartmentMap`, `[n • a] = n • [a]`.

*Orbit discreteness in `B(G)`.* Let `g ∈ G(F)` satisfy
`dist (g • [b]) [b] < ε`. Choose an apartment `h • A(S)` containing `[b]` and
`g • [b]`, say `[b] = h • [a₁]` and `g • [b] = h • [a₂]`. The quotient relation
gives `n₁, n₂ ∈ N(F)` with `n₁ • a₁ = b` and `n₂ • a₂ = b`. Then
`dist ((n₁ n₂⁻¹) • b) b = dist a₂ a₁ = dist (g • [b]) [b] < ε`. The hypothesis
on `N(F)` gives `(n₁ n₂⁻¹) • b = b`, so `a₂ = a₁` and `g • [b] = [b]`. For a
general point `g₀ • [b]` the element `g₀⁻¹ g g₀` is used. KP prove this
assertion for `G(k)⁰` from Lemma 4.2.11, first assertion (facets meeting a small ball), and
Proposition 1.5.13. Here the full group `G(F)` is treated and facets are not
used. Instead, the discreteness of `N(F)`-orbits in `A(S)` is the hypothesis.

*Completeness.* `completeSpace_of_isometry_apartmentMap` applies
`Metric.KP.completeSpace_of_discrete_orbits` (module
`Langlands.Geometry.Metric.DiscreteOrbitCompleteness`) with `Γ = G(F)`. The
compact set for the unit ball around `x₀ = g₀ • [b]` is the image of the
closed unit ball of `A(S)` around `b`, compact because `A(S)` is proper. If
`dist x x₀ < 1`, choose an apartment `h • A(S)` containing `x₀` and `x`, write
`x₀ = h • [a₀]` and `x = h • [a]`, and take `n ∈ N(F)` with `n • a₀ = b`. Then
`x = (h n⁻¹) • [n • a]` and `dist (n • a) b = dist a a₀ = dist x x₀ ≤ 1`. In
the source the compact set is the closure of a chamber and `G(k)⁰` acts. Here
the closed ball and the full group are used, which avoids chambers.

*The Euclidean apartment.* `apartment_properSpace`: the reduced translation
space is finite-dimensional (`RootTranslationMetric.finiteDimensional`), and
`A(S)` is isometric to it by `IsometryEquiv.vaddConst`.
`exists_forall_dist_normalizer_smul_lt_imp_eq` uses two fields of
`SatisfiesApartmentAxioms`: AS 3, that `Ψ` is an affine root system
(`isAffineRootSystem_affineRoots`, hence a locally finite reflection
arrangement), and AS 5, that the image of `N(F)` lies in `W(Ψ)ᵉˣᵗ`
(`range_le_extendedAffineWeylGroup`). `W(Ψ)ᵉˣᵗ` lies in the stabilizer of `Ψ`
(`AffineRootSystem.extendedAffineWeylGroup_le_rootStabilizer`).
`AffineRootSystem.exists_forall_dist_lt_imp_eq` (module
`Langlands.Geometry.Building.AffineRootOrbitDiscreteness`) shows that the
stabilizer of a locally finite arrangement has discrete orbits. This is the apartment step of Lemma 4.2.11, where the
source uses Axiom 4.1.6 and Proposition 1.3.12.

Sources: Kaletha–Prasad (2023), Theorem 4.2.10 and Lemma 4.2.11, printed
pp.171–172 / PDF pp.202–203, with the corrections of 1 November 2024,
Section 4.2 (which add Axiom 4.1.6 to the standing assumptions of 4.2). The
second assertion of Theorem 4.2.10, closedness of unions of facets, is not
treated. The first assertion of Lemma 4.2.11, about facets meeting a small
ball, is not proved here.

Author: Worker 1221.
