# Proof of the comparisons of KP Axiom 4.1.1 for all supplied valuation data

Module `Langlands.Geometry.Building.BuildingComparisonAxiomProof`.

`Langlands.Geometry.Building.buildingComparisonAxiom` proves the published
proposition `Langlands.Geometry.Building.BuildingComparisonAxiomStatement.{u}`
exactly, at arbitrary universe `u`, with no added hypothesis. The statement
covers every nonarchimedean local field `F` and arbitrary supplied
`ValuationBuildingData` on both sides of each comparison. For each of the
three clauses the proof gives `Φ : B.ReducedBuilding ≃ B'.ReducedBuilding`
with `ValuationBuildingData.IsEquivariantBuildingIso` along the given map of
rational points.

## Implemented proof

The theorem applies three results, one per clause.

1. **Central surjections.** For `f : G → G'` with `IsCentralSurjection f`:
   `ValuationBuildingData.exists_isEquivariantBuildingIso_centralSurjection`
   (module `Langlands.Geometry.Building.ValuationBuildingCentralSurjectionComparison`).
2. **Derived subgroups.** For `d : G_der → G` with `IsDerivedSubgroup d`:
   `ValuationBuildingData.exists_isEquivariantBuildingIso_derivedSubgroup`
   (module `Langlands.Geometry.Building.ValuationBuildingDerivedComparison`).
3. **Simply connected covers.** For `IsSimplyConnectedDerivedCover d π`, along
   `π ≫ d`:
   `ValuationBuildingData.exists_isEquivariantBuildingIso_simplyConnectedCover`
   (same module).

All three are built on one construction. A
`KPApartmentData.Transfer` from an apartment class of `G₁` to one of `G₂`
along `θ : G₁(F) →* G₂(F)` consists of:

- an affine equivalence of apartments, equivariant for the normalizers;
- `θ(G₁(F)^♯_x) = G₂(F)^♯_{e x}` for the sharp fixers;
- the correspondence of affine roots;
- the reflection `θ(g) ∈ N₂ → g ∈ N₁`;
- `G₂(F) = θ(G₁(F)) · N₂(F)`.

Such a transfer induces `[(g, x)] ↦ [(θ g, e x)]` on the quotients (7.6.2),
an equivariant building isomorphism (`Transfer.isEquivariantBuildingIso`,
module `ValuationBuildingQuotientMap`). In each case a transfer is
constructed to the target data:

- for (2) and (3), from the derived (and central-isogeny) pullback of the
  target's apartment class (module `ValuationBuildingPullbackComparison`);
- for (1), through the derived subgroups, where `f` restricts to a central
  isogeny, with the centralizer handled by V 6.

KP Fact 2.6.22 (`simplyConnectedCentralizerProduct`) gives the product
decompositions of `G(F)`. KP Proposition 6.2.6
(`omegaCompatibleApartmentUniqueness`) identifies the two derived apartment
classes in case (1). Arbitrary data on the source or target side are handled
by the same-group comparison of module
`ValuationBuildingSameGroupComparison`:

- `maximalSplitTorusConjugacy` conjugates the tori;
- `KPApartmentData.transport` moves the apartment class along the
  conjugation;
- Proposition 6.2.6 identifies the transported class with the class of the
  other datum;
- `IsEquivariantBuildingIso.exists_resource` and `exists_retarget` replace
  either datum by any other datum for the same group.

The supporting modules, in dependency order:

- `Langlands.Geometry.Building.ValuationBuildingQuotientMap`
- `Langlands.Geometry.Building.ValuationBuildingSameGroupComparison`
- `Langlands.Geometry.Building.ValuationBuildingPullbackComparison`
- `Langlands.Geometry.Building.ValuationBuildingDerivedComparison`
- `Langlands.GroupScheme.CentralSurjection.DerivedMap` and
  `Langlands.GroupScheme.CentralSurjection.TorusImage` (the group-scheme
  inputs of case (1): the central isogeny of derived subgroups, the image
  torus and the derived torus isogeny)
- `Langlands.Geometry.Building.ValuationBuildingCentralSurjectionComparison`

Their paired Markdown describes each proof.

## Scope

The proof uses only the statement's hypotheses and published Library results.
It assumes no V 7, AS 5, building-axiom witness, `IsAvailableFor` or other
unproved proposition. It constructs no valuation data. Inspection of the
compiled theorem reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The statement's Markdown records the source: Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Axiom 4.1.1 (printed pp.157–158 / PDF
pp.188–189) and (7.6.1) with Remark 7.6.5 (printed pp.264, 266 / PDF
pp.295, 297). KP obtain (7.6.1) from Tits systems (Lemma 1.4.13). This proof
instead compares the valuation quotients (7.6.2) directly, using KP
Proposition 6.2.6 (printed p.216) and Fact 2.6.22.
