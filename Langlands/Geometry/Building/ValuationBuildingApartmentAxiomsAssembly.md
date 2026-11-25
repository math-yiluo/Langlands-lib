# The apartment axioms of valuation building data, assembled

Lean module: `Langlands.Geometry.Building.ValuationBuildingApartmentAxiomsAssembly`,
namespace `Langlands.Geometry.Building`.

This module derives `ValuationBuildingApartmentAxiomsStatement` (module
`Langlands.Geometry.Building.UnramifiedValuationDescentStatement`) from the
single hypothesis `SimplyConnectedFacetFixingStatement` (module
`Langlands.Geometry.Building.SimplyConnectedFacetFixingStatement`), which
gives the simply connected sentence of AS 5. The hypothesis is proved in the
Library as `simplyConnectedFacetFixing` (module
`Geometry.Building.SimplyConnectedFacetFixingProof`); the unconditional
statement is `valuationBuildingApartmentAxioms` of the module
`Geometry.Building.ValuationBuildingApartmentAxiomsProof`.

## Declarations

```
theorem Langlands.Geometry.Building.ValuationBuildingData.satisfiesApartmentAxioms_of_facetFixing
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] (B : ValuationBuildingData G)
    (hfix : SimplyConnectedFacetFixingStatement.{u}) :
    B.SatisfiesApartmentAxioms

theorem Langlands.Geometry.Building.valuationBuildingApartmentAxioms_of_facetFixing
    (hfix : SimplyConnectedFacetFixingStatement.{u}) :
    ValuationBuildingApartmentAxiomsStatement.{u}
```

- `ValuationBuildingData.satisfiesApartmentAxioms_of_facetFixing`: for every
  `B : ValuationBuildingData G` over a nonarchimedean local field,
  `SimplyConnectedFacetFixingStatement` gives `B.SatisfiesApartmentAxioms`,
  that is V 6, V 7, AS 2–AS 4 and the three sentences of corrected AS 5 for the
  apartment of `B` and its centralizer.
- `valuationBuildingApartmentAxioms_of_facetFixing`:
  `SimplyConnectedFacetFixingStatement.{u}` implies
  `ValuationBuildingApartmentAxiomsStatement.{u}`, that is
  `∀ F … G … (B : ValuationBuildingData G), B.SatisfiesApartmentAxioms`.

## Proof

Each field of `KPApartmentData.SatisfiesApartmentAxioms` for `B.apartment` and
`B.centralizer` is filled from a result proved in the Library:

- V 6: the field `B.isOmegaCompatible` of the data.
- V 7: `ValuationBuildingData.isTopologyCompatible` (module
  `Geometry.Building.ValuationBuildingTopologyCompatible`).
- AS 2 (both parts), AS 3 (`Ψ` is an affine root system), AS 4 and the first
  sentence of AS 5 (both inclusions): the conjuncts of
  `valuationBuildingAffineRootSystems` (module
  `Geometry.Building.ValuationAffineRootSystems`). The proof does not use its
  fourth conjunct, `∇Ψ ⊆ Φ`.
- AS 3, `∇Ψ = Φ`:
  `ValuationBuildingData.derivativeRoots_affineRoots_of_isTopologyCompatible`
  (module `Geometry.Building.ValuationDerivativeAffineRoots`), applied to V 7.
- AS 5, simply connected sentence:
  `ValuationBuildingData.normalizerAffineEquiv_range_eq_affineWeylGroup_of_simplyConnectedFacetFixing`
  (module `Geometry.Building.SimplyConnectedApartmentWeylAction`), with the
  hypothesis `SimplyConnectedFacetFixingStatement`, AS 3 for `Ψ` and the
  opposite factor pairs `ValuationBuildingData.hasOppositeFactorPairs` (module
  `Geometry.Building.SimplyConnectedNormalizerAffineWeylAssembly`).
- AS 5, quasi-split adjoint sentence:
  `ValuationBuildingData.range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation`
  (module `Geometry.Building.ValuationQuasiSplitAdjointTranslation`), applied
  to `valuationBuildingQuasiSplitAdjointTranslation` (module
  `Geometry.Building.ValuationQuasiSplitAdjointTranslationProof`) and to both
  inclusions of the first sentence of AS 5.

The second theorem applies the first to every `B`.

## Literature

The assembly is internal: it combines results of the Library and adds no
claim from the literature. The statement it proves is T. Kaletha and
G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Chapter 9, §9.5,
printed pp. 363–364 (Axiom 4.1.6 for the descended building: AS 2 and AS 3 by
Proposition 9.4.19, AS 4 by Proposition 9.4.18, AS 5 by Proposition 9.4.35),
with the comparison of §9.6.6, printed p. 367, as described on the page of
`Geometry.Building.UnramifiedValuationDescentStatement`. The route differs from
the book's: V 7 and AS 2–AS 4 are proved for every `B` directly from V 0–V 6
(KP §6.3), and AS 5 from facet fixing for simply connected groups and from the
quasi-split adjoint translation theorem.
