import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.Index

/-! # Integral duals of restricted character lattices -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Plancherel.RenardCartan.IntegralRestriction

variable {B C M : Type*} [AddCommGroup B] [Module ℤ B]
  [AddCommGroup C] [Module ℤ C] [AddCommGroup M] [Module ℤ M]

attribute [-instance] AddCommGroup.toIntModule in
/-- Descend an integral functional vanishing on the restriction kernel to the
actual image of restriction. -/
def descend (r : M →ₗ[ℤ] B) :
    r.ker.dualAnnihilator ≃ₗ[ℤ] Module.Dual ℤ r.range :=
  r.ker.dualQuotEquivDualAnnihilator.symm.trans r.quotKerEquivRange.dualMap.symm

attribute [-instance] AddCommGroup.toIntModule in
@[simp] theorem descend_apply_rangeRestrict (r : M →ₗ[ℤ] B)
    (l : r.ker.dualAnnihilator) (m : M) :
    descend r l (r.rangeRestrict m) = l.val m := by
  change r.ker.dualCopairing l
    (r.quotKerEquivRange.symm ⟨r m, _⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

attribute [-instance] AddCommGroup.toIntModule in
/-- Injectivity into the dual of a sublattice of an equally ranked lattice
forces finite cokernel. -/
theorem finiteIndex_range_of_injective
    [Module.Free ℤ B] [Module.Finite ℤ B]
    (e : C ≃ₗ[ℤ] B) (A : Submodule ℤ B)
    (p : C →ₗ[ℤ] Module.Dual ℤ A) (hp : Function.Injective p) :
    p.range.toAddSubgroup.FiniteIndex := by
  have hdual : Module.finrank ℤ (Module.Dual ℤ A) = Module.finrank ℤ A :=
    (Module.Free.chooseBasis ℤ A).toDualEquiv.finrank_eq.symm
  have hupper : Module.finrank ℤ (Module.Dual ℤ A) ≤ Module.finrank ℤ C := by
    rw [hdual, e.finrank_eq]
    exact Submodule.finrank_le A
  have heq : Module.finrank ℤ p.range = Module.finrank ℤ (Module.Dual ℤ A) := by
    rw [LinearMap.finrank_range_of_inj hp]
    exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hp) hupper
  exact @AddSubgroup.finiteIndex_of_finite_quotient _ _ p.range.toAddSubgroup
    (Submodule.finiteQuotientOfFreeOfRankEq p.range heq)

end Langlands.Plancherel.RenardCartan.IntegralRestriction
