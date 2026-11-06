# Retractions of the building onto the base apartment

This module constructs, on the existing quotient `B(G) = P.ReducedBuilding`,
the retraction `ρ_{A,C} : B(G) → A(S)` of Kaletha–Prasad (2023),
Proposition 1.5.24 and Definition 1.5.25, for a chamber `C` of the base
apartment `A(S)`. It proves Lemma 4.2.2(3) and the case `x ∈ C̄` of Lemma
4.2.2(2) for every distance `d` on `B(G)` that is the Euclidean root metric in
every translated apartment chart. The main theorem `exists_apartmentRetraction` is exactly the
field `exists_retraction` of
`Langlands.Geometry.Building.ValuationBuildingData.IsRetractionBuildingDistance`
(module `Langlands.Geometry.Building.ValuationBuildingMetricAssembly`).

The module does not construct `d`. It does not prove the polysimplicial
properties of `ρ_{A,C}` (Proposition 1.5.24(2),(3)) or its uniqueness.

## Notation

`[a]` denotes `P.apartmentMap a` for `a : P.Apartment`, and `g • x` is the
action of `g ∈ G(F) = rationalPoints G` on `B(G)`. The apartments of `B(G)` are
the sets `g • A(S)` (`IsApartment`). `A(S)` carries the Euclidean root metric
`apartmentMetricSpace` of `Langlands.Geometry.Building.ValuationApartmentMetric`,
installed through local instances at the end of the module. The facet of
`y ∈ A(S)` is `AffineRootSystem.facet P.affineRoots y`. When `y` is regular
(`IsRegular`), this facet is a chamber.

## Declarations

| Lean name | Kind | Content |
| --- | --- | --- |
| `AffineRootSystem.apply_eq_of_forall_mem_facet_of_isRegular` | theorem | For a locally finite reflection arrangement, an affine automorphism `e` of `A` that fixes the chamber of a regular point `y` pointwise is the identity |
| `ValuationBuildingData.HasCompatibleApartmentFacets.subset_of_inter_nonempty` | theorem | Under AS 6, a facet of `B(G)` that meets an apartment `Y` lies in `Y` |
| `ParahoricBuildingData.translatedApartmentFacet g p` | def | The building facet `g • [F(p)]`, where `F(p)` is the facet of `p` in `A(S)` |
| `ParahoricBuildingData.smul_apartmentMap_mem_translatedApartmentFacet` | theorem | `g • [q] ∈ g • [F(p)]` for `q ∈ F(p)` |
| `ParahoricBuildingData.translatedApartmentFacet_precedes` | theorem | `q` in the closure of `F(p)` gives `FacetPrecedes (g • [F(q)]) (g • [F(p)])` |
| `ParahoricBuildingData.smul_apartmentMap_mem_of_mem_facetClosure` | theorem | An apartment containing `g • [p]` contains `g • [q]` for every `q` in the closure of `F(p)` |
| `ParahoricBuildingData.smul_eq_smul_of_forall_mem_facet` | theorem | If `y` is regular, `h₁`, `h₂` fix `[C]` pointwise (`C = F(y)`) and `h₁ • x`, `h₂ • x ∈ A(S)`, then `h₁ • x = h₂ • x` |
| `ParahoricBuildingData.exists_zero_forall_mem_facet_smul_eq` | theorem | Every apartment `Y ∋ [y]` is carried onto `A(S)` by some `r ∈ G(F)^0` fixing `[F(y)]` pointwise |
| `ParahoricBuildingData.smul_apartmentMap_eq_of_mem_facetClosure` | theorem | An `r ∈ G(F)^0` fixing `[F(y)]` pointwise fixes `[a]` for every `a` in the closure of `F(y)` |
| `ParahoricBuildingData.exists_retractionPoint` | theorem | For every `x ∈ B(G)` there are `b ∈ A(S)` and `r ∈ G(F)^0` fixing `[F(y)]` pointwise with `r • x = [b]` |
| `ParahoricBuildingData.chamberRetraction hD hcommon y` | def | `ρ_{A,C}(x)`: the point `b` chosen in `exists_retractionPoint` |
| `ParahoricBuildingData.apartmentMap_chamberRetraction` | theorem | For regular `y`, `[ρ_{A,C}(x)] = h • x` for every `h` fixing `[C]` pointwise with `h • x ∈ A(S)` |
| `ParahoricBuildingData.exists_apartmentRetraction` | theorem | Lemma 4.2.2(3) and the case `x ∈ C̄` of Lemma 4.2.2(2) for compatible `d`, see below |

The main theorem is

```
exists_apartmentRetraction hcommon hD hN hA hTits {d} hd a :
  ∃ ρ : P.ReducedBuilding → P.Apartment,
    (∀ b, ρ [b] = b) ∧
    (∀ x x', dist (ρ x) (ρ x') ≤ d x x') ∧
    ∀ x, dist a (ρ x) = d [a] x
```

Its hypotheses are:

* `hcommon : ∀ x, P.HasCommonApartmentWith x`: any two points lie in a common
  apartment (`HasCommonApartmentWith`, module
  `Langlands.Geometry.Building.ApartmentFixedPointReduction`; it follows from a
  realization's building axiom by `hasCommonApartmentWith_of_isBuilding`);
* `hD : P.SatisfiesApartmentAxioms`: V 7 and AS 2–AS 5 (KP Axiom 4.1.6);
* `hN : P.HasNormalizerApartmentStabilizer`: the stabilizer of `A(S)` is `N(F)`;
* `hA : P.HasCompatibleApartmentFacets`: AS 6;
* `hTits : P.HasTitsSystem`: KP Axiom 4.1.9 for every chamber of `A(S)`;
* `hd : ∀ g a b, d (g • [a]) (g • [b]) = dist a b`: `d` is the Euclidean root
  metric in every translated apartment chart `a ↦ g • [a]`.

No symmetry or triangle inequality is assumed for `d`.

The three conclusions are the identity of `ρ` on `A(S)` (Proposition
1.5.24(1)), Lemma 4.2.2(3), and the first case of Lemma 4.2.2(2). KP state
that case for `x` in the closure `C̄` of the chamber `C`, and it is the case used
in the proofs of Proposition 4.2.7 and Lemma 4.2.8. Here the centre `a` plays
the role of `x`: it is any point of `A(S)`, and `C` is chosen with `a ∈ C̄`.
Since `ρ [a] = a`, the third conclusion reads `dist (ρ [a]) (ρ x) = d [a] x`.
The other case of Lemma 4.2.2(2), two points in the closure of one facet, and
Lemma 4.2.2(1) are not stated in this module.

## Provenance

The construction follows the proof of KP Proposition 1.5.24, rewritten in terms
of the group action. KP take an apartment `A'` containing `C` and the point,
and use the unique isomorphism `A' → A` fixing every vertex of `C`. Here this
isomorphism is the action of an element of `G(F)^0` that carries `A'` onto
`A(S)` and fixes `C` pointwise, as in KP's proof of Lemma 4.2.2(1). The
independence of the choice uses the Tits-system transport of two facets
between two apartments (`IsBuildingTitsSystem.exists_twoFacet_smul_apartment_eq`,
module `Langlands.Geometry.Building.TitsFacetApartmentTransport`), as KP use
BL 4. Lemma 4.2.2 is proved for an abstract compatible `d` instead of KP's
distance. Only the chart compatibility `hd` is used, which KP get from the
definition of `d` in Proposition 4.2.1.

## Proofs as implemented

*Chamber fixation.* `apply_eq_of_forall_mem_facet_of_isRegular`: `e` fixes `y`.
For every direction `v`, a short segment `y + εv` lies in the chamber of `y`
(`eventually_sign_smul_vadd`), so `e.linear (εv) = εv` and `e.linear v = v`.

*Facets meet apartments.* `subset_of_inter_nonempty` translates by `g⁻¹` to the
base apartment and applies the AS 6 field `exists_isFacet_of_isFacet`.

*Facet closures in apartments.* `smul_apartmentMap_mem_of_mem_facetClosure`:
the facet `g • [F(p)]` lies in `g • A(S)` and, by AS 6, in `Y`. The Tits-system
transport gives `k ∈ G(F)^0` stabilizing `g • [F(p)]` with `k • (g • A(S)) = Y`.
By `facetPrecedes_iff`, `k` also stabilizes the face `g • [F(q)]`.
`facetZeroStabilizer_smul_eq` (module
`Langlands.Geometry.Building.PointwiseFacetStabilizers`) then shows that `k`
fixes `g • [q]`, so `g • [q] = k • g • [q] ∈ Y`.

*Well-definedness.* `smul_eq_smul_of_forall_mem_facet`: both apartments
`h₁⁻¹ • A(S)` and `h₂⁻¹ • A(S)` contain `[C]` and `x`. Take a facet `F_x ∋ x` in
`h₁⁻¹ • A(S)`; by AS 6 it lies in `h₂⁻¹ • A(S)`. The Tits-system transport gives
`k ∈ G(F)^0` stabilizing `[C]` and `F_x` with `k • h₂⁻¹ • A(S) = h₁⁻¹ • A(S)`.
By `facetZeroStabilizer_smul_eq`, `k` fixes `x` and `[C]` pointwise. Then
`m = h₁ k h₂⁻¹` stabilizes `A(S)`, so `m ∈ N(F)` by `hN`, and its affine action
on `A(S)` fixes `C` pointwise. By chamber fixation it is the identity on
`A(S)`, so `h₁ • x = m • h₂ • x = h₂ • x`.

*Existence.* `exists_zero_forall_mem_facet_smul_eq` uses the sharp fixer of
the facet of `y` (`exists_sharpFixer_facet_smul_apartmentImage`) and the
inclusion of the sharp fixer in `G(F)^0` (`sharpFixer_le_simplyConnectedImage`,
`simplyConnectedImage_le_zeroSubgroup`). `exists_retractionPoint` applies it
to a common apartment of `[y]` and `x`. `chamberRetraction` chooses the point,
and `apartmentMap_chamberRetraction` combines the choice with
well-definedness.

*Closure points.* `smul_apartmentMap_eq_of_mem_facetClosure`: `r` stabilizes
the facet `[F(y)]`, hence the face `[F(a)]` by `facetPrecedes_iff`, and
`facetZeroStabilizer_smul_eq` fixes `[a]`.

*Lemma 4.2.2.* In `exists_apartmentRetraction`, choose a regular `y` with `a`
in the closure of its chamber (`exists_regularPoint_closure`) and the Tits
system of that chamber from `hTits`, and put `ρ = chamberRetraction hD hcommon y`.
If `h` fixes `[C]` pointwise and carries `x`, `x'` into `A(S)`, then
`dist (ρ x) (ρ x') = d x x'`, by `hd` at `h⁻¹`.

* `ρ [b] = b`: take `h = 1`; `[·]` is injective by AS 6.
* Nonexpansion: put `x = g • [p]`, `x' = g • [q]` in a common apartment
  `g • A(S)`. By `AffineRootSystem.dist_le_of_forall_mem_facetClosure`
  (module `Langlands.Geometry.Building.FacetClosureLipschitz`), it suffices
  that `u ↦ ρ (g • [u])` does not increase distances between two points `u`, `v`
  of the closure of one facet `F(p₀)`. Take an apartment `Y'` containing `[y]`
  and `g • [p₀]`, and `r` carrying `Y'` onto `A(S)` and fixing `[C]` pointwise.
  Then `Y'` contains `g • [u]` and `g • [v]`, so
  `dist (ρ (g • [u])) (ρ (g • [v])) = d (g • [u]) (g • [v]) = dist u v`. This
  replaces KP's subdivision of the segment `[x, y]` into pieces lying in facet
  closures.
* Distance from `a`: take `r` for a common apartment of `[y]` and `x`. It fixes
  `[a]` by the closure-point lemma, so
  `dist a (ρ x) = d (r⁻¹ • [a]) (r⁻¹ • [ρ x]) = d [a] x`.
