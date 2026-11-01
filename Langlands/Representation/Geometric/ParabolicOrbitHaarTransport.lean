import Langlands.HarmonicAnalysis.HaarConjugacy
import Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient
import Langlands.Representation.Geometric.GeneralCorrectionCharacters
import Langlands.Representation.Parabolic.UnipotentFiniteContainment

/-! Topological transport from the actual orbit kernels to ambient matrix subgroups. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Induction MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uF

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

omit [IsTopologicalRing F] in
@[simp] theorem parabolicOrbitRadicalAmbientEquiv_apply (u : C.unipotentRadical F) :
    (C.unipotentRadicalAmbientEquiv F u : GeneralLinear n F) = u.val.val := rfl

/-- The radical-stabilizer intersection is the literal target correction subgroup. -/
def parabolicOrbitIntersectionAmbientEquiv :
    parabolicOrbitRadicalIntersection F B C w ≃ₜ*
      intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
        (permutation n F w)⁻¹ where
  toFun u := ⟨u.val.val.val, ⟨u.val.val, u.val.property, rfl⟩, u.property⟩
  invFun u := ⟨(C.unipotentRadicalAmbientEquiv F).symm ⟨u.val, u.property.1⟩,
    u.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((C.unipotentRadicalAmbientEquiv F).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

omit [IsTopologicalRing F] in
@[simp] theorem parabolicOrbitIntersectionAmbientEquiv_apply
    (u : parabolicOrbitRadicalIntersection F B C w) :
    (parabolicOrbitIntersectionAmbientEquiv F B C w u : GeneralLinear n F) =
      u.val.val.val := rfl

/-- The actual nested kernel has the same topology as the ambient target radical. -/
def parabolicOrbitNestedKernelAmbientEquiv :
    (parabolicOrbitStagesRetraction F B C w).ker ≃ₜ* C.unipotentSubgroup F :=
  (splitStagesKernelContinuousEquiv (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStages_kernel_le F B C w)).trans
      (C.unipotentRadicalAmbientEquiv F)

/-- Removing all intermediate subtypes identifies the actual nested intersection
with the literal target correction subgroup. -/
def parabolicOrbitNestedIntersectionAmbientEquiv :
    parabolicOrbitNestedIntersection F B C w ≃ₜ*
      intersectionSource (C.unipotentSubgroup F) (B.parabolic F)
        (permutation n F w)⁻¹ :=
  (splitStagesIntersectionContinuousEquiv (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStabilizer F B C w) (parabolicOrbitStages_kernel_le F B C w)).trans
      (parabolicOrbitIntersectionAmbientEquiv F B C w)

end Langlands.Geometric
