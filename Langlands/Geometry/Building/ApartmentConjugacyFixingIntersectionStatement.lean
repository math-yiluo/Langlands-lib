import Langlands.Geometry.Building.FullValidity.Assignment

/-! # Two apartments are `G(F)^0`-conjugate by an element fixing their intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- KP Proposition 4.2.24 on supplied data satisfying the five axioms of the corrected opening
of KP Section 4.2 (Axioms 4.1.1 for `G` alone, 4.1.2, 4.1.4, 4.1.6 and 4.1.9).

For any two apartments `A₁`, `A₂` of the existing quotient `B(G)`, that is, `G(F)`-translates
of the apartment `A(S)`, there is `g ∈ G(F)^0` with `g · A₁ = A₂` that fixes every point of
`A₁ ∩ A₂`. No existence of the supplied data or of the axiom witnesses is asserted. -/
def ApartmentConjugacyFixingIntersectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting),
    P.SatisfiesBuildingAxiom R →
    P.HasBoundedOpenStabilizers →
    P.SatisfiesAffineApartmentAxiom T →
    P.HasRootReflections →
    P.SatisfiesApartmentAxioms →
    P.HasCompatibleApartmentFacets →
    P.HasTitsSystem →
    ∀ A₁ A₂ : Set P.toValuationBuildingData.ReducedBuilding,
      P.IsApartment A₁ → P.IsApartment A₂ →
        ∃ g ∈ P.zeroSubgroup, g • A₁ = A₂ ∧ ∀ y ∈ A₁ ∩ A₂, g • y = y

end Langlands.Geometry.Building
