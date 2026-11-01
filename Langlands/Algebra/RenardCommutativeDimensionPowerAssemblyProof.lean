import Langlands.Algebra.RenardCommutativeDimensionPowerAssemblyStatement
import Langlands.Algebra.RenardCommutativeEndomorphismDimensionProof

open scoped BigOperators

namespace Langlands.Renard

/-- Renard C.I: the exact source power is convex and bounds finite sums of powers. -/
theorem commutativeDimensionPowerAssembly :
    CommutativeDimensionPowerAssemblyStatement := by
  intro l hl
  have hr : 1 ≤ 2 - Real.rpow 2 (1 - (l : ℝ)) := by
    rw [renardExponent_eq_dimensionExponent]
    cases l with
    | zero => omega
    | succ k => exact CommutingDimension.dimensionExponent_succ_ge_one k
  refine ⟨hr, convexOn_rpow hr, ?_⟩
  intro n x hx
  simpa only [Real.rpow_eq_pow] using
    CommutingDimension.sum_rpow_le Finset.univ x _ (fun i _ => hx i) hr

end Langlands.Renard
