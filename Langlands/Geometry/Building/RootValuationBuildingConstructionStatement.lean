import Langlands.Geometry.Building.FullValidity.Assignment

/-! # Existence of the actual quotient and the metric-construction axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Construct the actual root-valuation quotient data and the five axiom
witnesses used by the corrected KP Section 4.2, for every connected reductive
group over a nonarchimedean local field. No such datum or witness is assumed.
This target omits the additional axioms of full corrected availability. -/
def RootValuationBuildingConstructionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∃ (P : ParahoricBuildingData G)
      (R : P.toValuationBuildingData.PolysimplicialRealization)
      (T : P.toValuationBuildingData.ApartmentSplitting),
      P.SatisfiesBuildingAxiom R ∧
      P.HasBoundedOpenStabilizers ∧
      P.SatisfiesAffineApartmentAxiom T ∧
      P.HasRootReflections ∧
      P.SatisfiesApartmentAxioms ∧
      P.HasCompatibleApartmentFacets ∧
      P.HasTitsSystem

end Langlands.Geometry.Building
