import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.RealDeriv

/-! # A nonzero smooth compact spectral coefficient in every dimension -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Global

/-- A smooth compactly supported complex scalar coefficient with value `1` at the origin.
It is the real bump of inner radius `1` and outer radius `2`, viewed in `ℂ`. -/
def spectralBump (m : ℕ) :
    {b : (Fin m → ℝ) → ℂ // ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ b 0 = 1} := by
  let β : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨Complex.ofRealCLM ∘ β, Complex.ofRealCLM.contDiff.comp β.contDiff,
    β.hasCompactSupport.comp_left rfl, ?_⟩
  change Complex.ofReal (β 0) = 1
  simp only [β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le), Complex.ofReal_one]

end Langlands.Global
