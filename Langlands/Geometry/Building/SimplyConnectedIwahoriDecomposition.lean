import Langlands.Geometry.Building.IwahoriDecompositionAxiomReduction
import Langlands.Geometry.Building.SimplyConnectedChamberNormalizer

/-! # Iwahori decomposition for a simply connected ambient group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The full Iwahori decomposition holds for supplied apartment-axiom data
whose ambient group is simply connected. -/
theorem hasIwahoriDecomposition_of_isSimplyConnected
    (hP : P.SatisfiesApartmentAxioms) (hG : IsSimplyConnected G) :
    P.HasIwahoriDecomposition := by
  intro C hC ν hν
  exact P.isIwahoriDecompositionAt_of_forall_mem_normalizerZero hP hC
    (fun n hn hnC =>
      P.mem_normalizerZero_of_stabilizes_chamber_of_isSimplyConnected hP hG hC n hn hnC)
    hν

end ParahoricBuildingData

/-- The simply connected ambient-group case of KP Axiom 4.1.16,
at arbitrary universe and for every supplied datum satisfying the apartment axioms. -/
def SimplyConnectedIwahoriDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    P.SatisfiesApartmentAxioms → IsSimplyConnected G → P.HasIwahoriDecomposition

/-- The published chamber-normalizer theorem discharges the premise of the
published local Iwahori assembly in the simply connected case. -/
theorem simplyConnectedIwahoriDecomposition :
    SimplyConnectedIwahoriDecompositionStatement.{u} := by
  intro F _ _ _ _ G _ P hP hG
  exact P.hasIwahoriDecomposition_of_isSimplyConnected hP hG

end Langlands.Geometry.Building
