import Langlands.Geometry.Building.IwahoriWeylChamberLemmas
import Langlands.Geometry.Building.AffineChamberTransitivity

/-! # Chamber splitting from the actual Iwahori–Weyl exact sequence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- AS3 specializes the proved generic chamber theorem to the actual apartment. -/
theorem existsUnique_affineWeyl_chamber_transport
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (C D : Set P.Apartment)
    (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (hD : AffineRootSystem.IsChamber P.affineRoots D) :
    ∃! w : AffineRootSystem.affineWeylGroup P.affineRoots,
      (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C = D :=
  affineChamberSimpleTransitivity _ P.Apartment P.affineRoots
    hP.isAffineRootSystem_affineRoots C D hC hD

/-- The actual exact sequence implies chamber splitting, with generic
simple transitivity supplied by its published proof. -/
theorem iwahoriWeylChamberSplitting_of_exactSequence
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hex : P.IwahoriWeylExactSequence)
    (C : Set P.Apartment) (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    P.IwahoriWeylChamberSplitting C :=
  P.iwahoriWeylChamberSplitting_of_unique_chamber_transport hP hex
    (P.existsUnique_affineWeyl_chamber_transport hP) C hC

end ParahoricBuildingData

/-- The remaining global algebraic exact-sequence target implies the unchanged
global chamber-splitting target. -/
def IwahoriWeylChamberExactSequenceReductionStatement : Prop :=
  IwahoriWeylExactSequenceStatement.{u} → IwahoriWeylChamberSplittingStatement.{u}

theorem iwahoriWeylChamberExactSequenceReduction :
    IwahoriWeylChamberExactSequenceReductionStatement.{u} := by
  intro hex F _ _ _ _ G _ P hP C hC
  exact P.iwahoriWeylChamberSplitting_of_exactSequence hP (hex F G P hP) C hC

end Langlands.Geometry.Building
