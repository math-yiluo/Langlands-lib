import Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame

/-! # Evaluation formulas for genuine dual-frame coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ} {U V W : S.Opens}

/-- The coordinate functional of the genuine dual frame evaluates a primal basis section. -/
lemma dual_localBasisCoordinate (e : LocalFrame M n U) (i : Fin (n + 1)) :
    localBasisCoordinate e.dual ⟨i⟩ =
      localDualEvaluation (localBasisSection e ⟨i⟩) := by
  classical
  simp only [localBasisCoordinate, dual, dualLocalFreeIso, dualLocalFreeInv,
    Preadditive.sum_comp, Category.assoc, ιFree_freeCoordinate, comp_ite,
    Category.comp_id, Limits.comp_zero]
  simp

/-- Coordinates in the actual dual frame are evaluations on the original basis. -/
lemma dual_coordinates_apply (e : LocalFrame M n U) (h : V ≤ U)
    (f : Γ(Langlands.Scheme.Modules.dual M, V)) (i : Fin (n + 1)) :
    e.dual.coordinates V h f i =
      dualEval M V f
        ((localBasisSection e ⟨i⟩).val (op (Over.mk (homOfLE h)))) := by
  rw [coordinates_apply, dual_localBasisCoordinate]
  rfl

set_option linter.defProp false in
/-- A coefficient of the dual-frame change is the transposed reverse primal coefficient. -/
def dual_change_single (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hWU : W ≤ U) (hWV : W ≤ V) (i j : Fin (n + 1)) :
    e.dual.change f.dual W hWU hWV (Pi.single j 1) i =
      f.change e W hWV hWU (Pi.single i 1) j := by
  rw [change, LinearEquiv.trans_apply, dual_coordinates_apply,
    coordinates_symm_single]
  change dualEval M W
      (e.dual.hom.val.app (op (Over.mk (homOfLE hWU)))
        ((SheafOfModules.freeSection ⟨j⟩).val (op (Over.mk (homOfLE hWU))))) _ = _
  rw [dual, dualLocalFreeIso_basis]
  change LocalHom.app (localBasisCoordinate e ⟨j⟩) (homOfLE hWU)
      ((localBasisSection f ⟨i⟩).val (op (Over.mk (homOfLE hWV)))) = _
  rw [change, LinearEquiv.trans_apply, coordinates_symm_single]
  rfl

end Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame
