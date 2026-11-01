import Langlands.Global.ArchimedeanCompactTypeClosureTransferStatement
import Langlands.Global.ArchimedeanCompactTypeClosureTransfer

/-! # Exact closure transfer for actual compact-type intersections -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Continuous actual compact-type projectors give closure transfer. -/
theorem compactTypeClosureTransfer : CompactTypeClosureTransferStatement K n := by
  intro M h_invariant h_finite σ h_dimension
  let := h_dimension
  exact compactType_inf_topologicalClosure_eq K n M h_invariant h_finite σ

end Langlands.Global.ArchimedeanGL
