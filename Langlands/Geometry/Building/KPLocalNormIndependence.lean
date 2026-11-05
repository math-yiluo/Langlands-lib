import Langlands.Geometry.Building.KPNormTowerImage
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Independence of the local bounded norm image from its splitting field -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) E] [IsGalois (UnramifiedClosure F) E]
  [FiniteDimensional (UnramifiedClosure F) M] [IsGalois (UnramifiedClosure F) M]
  (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffine T.X.left]

/-- The prescribed local norms have equal images for nested finite Galois splitting fields. -/
theorem torusNormIwahori_eq_of_le (h : E ≤ M)
    (hT : IsSplitTorus (baseChanged (UnramifiedClosure F) E T.toGrp)) :
    torusNormIwahori (UnramifiedClosure F) M (intermediateValuation F M) T =
      torusNormIwahori (UnramifiedClosure F) E (intermediateValuation F E) T := by
  let : Algebra E M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : Module E M := Algebra.toModule
  have : IsScalarTower (UnramifiedClosure F) E M := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E M := FiniteDimensional.right (UnramifiedClosure F) E M
  have : IsGalois E M := IsGalois.tower_top_of_isGalois (UnramifiedClosure F) E M
  let : Module E (IntermediateField.extendScalars h) := inferInstanceAs (Module E M)
  have : FiniteDimensional E (IntermediateField.extendScalars h) :=
    inferInstanceAs (FiniteDimensional E M)
  have : (intermediateValuation F E).HasExtension (intermediateValuation F M) :=
    nestedIntermediateValuation_extends F E (IntermediateField.extendScalars h)
  exact torusNormIwahori_eq_of_tower (UnramifiedClosure F) E M
    (intermediateValuation F E) (intermediateValuation F M)
    (nestedIntermediateValuation_conjugate F E (IntermediateField.extendScalars h))
    (nestedIntermediate_unit_norm_surjective F E (IntermediateField.extendScalars h)) T hT

/-- Any two finite Galois splitting fields in the separable closure give the same image. -/
theorem torusNormIwahori_eq_of_splitting_fields
    (hE : IsSplitTorus (baseChanged (UnramifiedClosure F) E T.toGrp))
    (hM : IsSplitTorus (baseChanged (UnramifiedClosure F) M T.toGrp)) :
    torusNormIwahori (UnramifiedClosure F) E (intermediateValuation F E) T =
      torusNormIwahori (UnramifiedClosure F) M (intermediateValuation F M) T := by
  let P := E ⊔ M
  have : FiniteDimensional (UnramifiedClosure F) P := inferInstance
  have : IsGalois (UnramifiedClosure F) P := inferInstance
  exact (torusNormIwahori_eq_of_le F E P T le_sup_left hE).symm.trans
    (torusNormIwahori_eq_of_le F M P T le_sup_right hM)

/-- The actual norm-image subgroups are identified by the identity on torus points. -/
def localTorusNormEquiv
    (hE : IsSplitTorus (baseChanged (UnramifiedClosure F) E T.toGrp))
    (hM : IsSplitTorus (baseChanged (UnramifiedClosure F) M T.toGrp)) :
    torusNormIwahori (UnramifiedClosure F) E (intermediateValuation F E) T ≃*
      torusNormIwahori (UnramifiedClosure F) M (intermediateValuation F M) T :=
  MulEquiv.subgroupCongr (torusNormIwahori_eq_of_splitting_fields F E M T hE hM)

@[simp] theorem localTorusNormEquiv_coe
    (hE : IsSplitTorus (baseChanged (UnramifiedClosure F) E T.toGrp))
    (hM : IsSplitTorus (baseChanged (UnramifiedClosure F) M T.toGrp))
    (t : torusNormIwahori (UnramifiedClosure F) E (intermediateValuation F E) T) :
    (localTorusNormEquiv F E M T hE hM t : rationalPoints T.toGrp) = t := rfl

end Langlands.Geometry.Building
