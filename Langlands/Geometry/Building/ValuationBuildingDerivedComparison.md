# Reduced buildings of the derived subgroup and of its simply connected cover

Module `Langlands.Geometry.Building.ValuationBuildingDerivedComparison`.

Over a nonarchimedean local field `F`, this module proves the second and third
comparison clauses of `BuildingComparisonAxiomStatement` for arbitrary
supplied valuation-building data on both sides.

## Auxiliary results

- `map_comp_rationalPoints π d`: `(map d).comp (map π) = map (π ≫ d)` on
  rational points (over any field).
- `exists_eq_map_mul_normalizer B d π hdπ g`: for `B : ValuationBuildingData G`
  and a simply connected derived cover `d : D → G`, `π : C → D`, every
  `g ∈ G(F)` is `(π ≫ d)(c) · n` with `c ∈ C(F)` and `n` in the normalizer
  `N(F)` of the torus of `B`. This is KP Fact 2.6.22 in the published form
  `simplyConnectedCentralizerProduct`, applied to the centralizer datum of
  `B`. Its centralizer part lies in `N(F)` by `map_mem_centralizerPoints` and
  `centralizerPoints_le_normalizerPoints`.

## The derived subgroup

`exists_isEquivariantBuildingIso_derivedSubgroup d hd B B'`: for
`hd : IsDerivedSubgroup d`, `d : G_der → G`, and arbitrary
`B : ValuationBuildingData G_der` and `B' : ValuationBuildingData G`, there is
`Φ : B.ReducedBuilding ≃ B'.ReducedBuilding` with
`IsEquivariantBuildingIso B B' (rationalPoints.map d) Φ`.

Proof.

1. *Structural tori.* `derivedMaximalSplitTorus` gives a maximal split torus
   `j : T → G_der` and a closed `e : T → S'` with `j ≫ d = e ≫ i'`, where
   `i' : S' → G` is the torus of `B'`. The split component of `G`
   (`splitComponentStatement`, `exists_commFactor_of_isMaximalSplitTorus`)
   gives a central split torus `c : A → S'`. By
   `derivedCentralSplitTorusProduct` the product `T × A → S'` is a central
   isogeny, hence flat and surjective.
2. *Source data.* The class `X` is the derived pullback of the apartment class
   of `B'` (`KPApartmentData.derivedPullback`). With the centralizer datum
   `CentralizerDatum.ofValuationComparison` of `j` (from
   `Cartan.centralizerValuationComparison`) and V 6 from
   `IsOmegaCompatible.derivedPullback`, this gives valuation-building data
   `BX` of `G_der` with torus `j` and apartment class `X`.
3. *Transfer.* A `KPApartmentData.Transfer` from `X` to the class of `B'`
   along `rationalPoints.map d` consists of:
   - the comparison `derivedComparison` (module
     `ValuationBuildingPullbackComparison`);
   - normalizer reflection, `d(g) ∈ N(F) → g ∈ N_{G_der}(T)(F)`, by
     `DerivedCoverNormalizerLift.mem_normalizerPoints` applied to the
     identity `𝟙 G_der` (a central isogeny by `isCentralIsogeny_of_isIso`);
   - `G(F) = d(G_der(F)) · N(F)`, from `exists_eq_map_mul_normalizer`. The
     simply connected cover comes from `simplyConnectedCoverExistence` for
     the semisimple `G_der` (`derivedSubgroupSemisimple`).
4. `Transfer.isEquivariantBuildingIso` gives the isomorphism from `BX` to
   `B'`. `IsEquivariantBuildingIso.exists_resource` (module
   `ValuationBuildingSameGroupComparison`) replaces `BX` by the given `B`.

## The simply connected cover

`exists_isEquivariantBuildingIso_simplyConnectedCover d π hdπ B B'`: for
`hdπ : IsSimplyConnectedDerivedCover d π`, `π : G_sc → G_der`, and arbitrary
`B : ValuationBuildingData G_sc` and `B' : ValuationBuildingData G`, there is
`Φ` with `IsEquivariantBuildingIso B B' (rationalPoints.map (π ≫ d)) Φ`.

The proof is the same with one more stage.
`simplyConnectedDerivedCoverSplitTorus` gives `j : T → G_der`, `e`, a maximal
split torus `k : U → G_sc` and an isogeny `f : U → T` with `k ≫ π = f ≫ j`
and `k ≫ π ≫ d = (f ≫ e) ≫ i'`. The class of `G_sc` is the central-isogeny
pullback through `π` of the derived pullback `X`, and its V 6 comes from
`IsOmegaCompatible.centralIsogenyPullback`. This class is the same as in
`ParahoricBuildingData.derivedCoverValuationBuildingData`, here built from `B'`.
The Transfer's comparison is `centralIsogenyComparison` followed by
`derivedComparison` (`Comparison.trans`), with its homomorphism rewritten to
`rationalPoints.map (π ≫ d)` by `map_comp_rationalPoints`
(`Comparison.congrHom`). Normalizer reflection is
`DerivedCoverNormalizerLift.mem_normalizerPoints` for `π` and `d`.
`G(F) = (π ≫ d)(G_sc(F)) · N(F)` is `exists_eq_map_mul_normalizer`.

## Provenance

The theorems are clauses (2) and (3) of the Library statement
`BuildingComparisonAxiomStatement`, which records the source:
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Axiom 4.1.1
(printed pp.157–158) and (7.6.1) with Remark 7.6.5 (printed pp.264, 266). KP
deduce (7.6.1) from Tits systems (Lemma 1.4.13). This proof compares the
valuation quotients (7.6.2) directly. It uses KP Fact 2.6.22
(`simplyConnectedCentralizerProduct`) for surjectivity. Independence of the
choice of data uses Proposition 6.2.6 and the conjugacy of maximal split tori,
through `exists_resource`.
