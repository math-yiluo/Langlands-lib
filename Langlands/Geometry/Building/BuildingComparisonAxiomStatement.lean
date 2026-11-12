import Langlands.Geometry.Building.FullValidity.Assignment

/-! # The comparisons of Axiom 4.1.1 for all supplied valuation data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The comparisons between groups in KP Axiom 4.1.1, for arbitrary supplied valuation data on
both sides, over a nonarchimedean local field `F`:

* every surjective homomorphism `f : G → G'` with central kernel induces an isomorphism of
  buildings `Φ : B(G) → B(G')` with `Φ(g · y) = f(g) · Φ(y)`;
* for every derived subgroup `d : G_der → G` there is an isomorphism of buildings
  `Φ : B(G_der) → B(G)` with `Φ(h · y) = d(h) · Φ(y)`;
* for every derived subgroup `d : G_der → G` and simply connected cover `π : G_sc → G_der`
  there is an isomorphism of buildings `Φ : B(G_sc) → B(G)` with `Φ(h · y) = d(π(h)) · Φ(y)`.

Here `B(G)` is the existing quotient of any `ValuationBuildingData` for the group. These are
the clauses `HasCentralQuotientComparisons`, `HasDerivedSubgroupIdentification` and
`HasSimplyConnectedCoverIdentification` of `KPBuildingAssignment`, asserted for every choice of
data. No existence of data is asserted. -/
def BuildingComparisonAxiomStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    (∀ (G G' : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [IsAffineHom G'.X.hom] (f : G ⟶ G'), IsCentralSurjection f →
        ∀ (B : ValuationBuildingData G) (B' : ValuationBuildingData G'),
          ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
            ValuationBuildingData.IsEquivariantBuildingIso B B' (rationalPoints.map f) Φ) ∧
    (∀ (G Gder : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [IsAffineHom Gder.X.hom] (d : Gder ⟶ G), IsDerivedSubgroup d →
        ∀ (B : ValuationBuildingData Gder) (B' : ValuationBuildingData G),
          ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
            ValuationBuildingData.IsEquivariantBuildingIso B B' (rationalPoints.map d) Φ) ∧
    (∀ (G Gder Gsc : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [IsAffineHom Gsc.X.hom] (d : Gder ⟶ G) (π : Gsc ⟶ Gder),
        IsSimplyConnectedDerivedCover d π →
        ∀ (B : ValuationBuildingData Gsc) (B' : ValuationBuildingData G),
          ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
            ValuationBuildingData.IsEquivariantBuildingIso B B'
              (rationalPoints.map (π ≫ d)) Φ)

end Langlands.Geometry.Building
