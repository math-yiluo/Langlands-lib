import Langlands.Algebra.SmoothEqualizerFibreCriterion
import Langlands.Algebra.CechEqualizer.Criterion

/-! # Proof of the fibrewise criterion for equalizers of smooth algebras -/

universe u

namespace Langlands.Algebra

/-- The fibrewise criterion for equalizers of smooth algebras holds in every universe. -/
theorem smoothEqualizerFibreCriterion : SmoothEqualizerFibreCriterion.{u} := by
  intro A C₀ C₁ _ _ _ _ _ δ₁ δ₂ h₀ h₁ hff hfib c hc
  exact CechEqualizer.mem_range_of_smooth δ₁ δ₂ hfib c hc

end Langlands.Algebra
