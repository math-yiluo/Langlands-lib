import Langlands.Global.RankinSelberg.ComplexLocalDualConvergence
import Langlands.Global.RankinSelberg.ComplexUnequalAnalyticReduction

/-! # Reduction to the normalized complex unequal-rank equation -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Absolute convergence on a shared half-plane for every pair of intertwiner values. -/
theorem complexUnequalIntertwinerConvergence : ComplexUnequalIntertwinerConvergenceStatement := by
  intro r t h d d' _ _ a D B B' hB hB' f f'
  exact complexLocalUnequalConvergence h d d' a D
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
    ⟨B' f', Submodule.mem_iSup_of_mem B' (Submodule.mem_iSup_of_mem hB' ⟨f', rfl⟩)⟩

/-- The normalized equation on intertwiner values implies the target on the two full models. -/
def ComplexLocalUnequalFromNormalizedStatement : Prop :=
  ComplexUnequalNormalizedIntertwinerEquationStatement →
    ComplexLocalUnequalFunctionalEquationStatement

theorem complexLocalUnequalFromNormalized : ComplexLocalUnequalFromNormalizedStatement :=
  complexUnequalAnalyticReduction complexUnequalIntertwinerConvergence

end Langlands.Global.RankinSelbergGlobal
