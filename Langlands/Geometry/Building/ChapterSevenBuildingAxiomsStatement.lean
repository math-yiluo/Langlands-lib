import Langlands.Geometry.Building.FullValidity.Assignment

/-! # The Chapter 7 building of supplied valuation data satisfies the Section 4.2 axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Geometry.Building

/-- The main output of KP Chapter 7 on supplied data over a nonarchimedean local field: if the
class `A(S)` of `P : ParahoricBuildingData G` satisfies V 7 and AS 2–AS 5
(`P.SatisfiesApartmentAxioms`; V 6 is part of the data), then the existing quotient `B(G)` has a
polysimplicial structure `R` and the apartment a splitting `T` such that Axiom 4.1.1 for `G` alone,
Axioms 4.1.2 and 4.1.4, AS 1 and AS 6 of Axiom 4.1.6, and Axiom 4.1.9 hold. Together with the
premise these are the seven Library predicates of the corrected opening of KP Section 4.2. No
existence of the data is asserted. -/
def ChapterSevenBuildingAxiomsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    P.SatisfiesApartmentAxioms →
      ∃ (R : P.toValuationBuildingData.PolysimplicialRealization)
        (T : P.toValuationBuildingData.ApartmentSplitting),
        P.SatisfiesBuildingAxiom R ∧
        P.HasBoundedOpenStabilizers ∧
        P.SatisfiesAffineApartmentAxiom T ∧
        P.HasRootReflections ∧
        P.HasCompatibleApartmentFacets ∧
        P.HasTitsSystem

end Langlands.Geometry.Building
