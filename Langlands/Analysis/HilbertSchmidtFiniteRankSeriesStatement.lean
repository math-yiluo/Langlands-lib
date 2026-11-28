import Langlands.Analysis.OperatorIdeals

/-! # A Hilbert–Schmidt criterion for series of finite-rank operators -/

set_option autoImplicit false

namespace Langlands.Analysis.OperatorIdeals

universe u v

/-- An operator-norm sum of finite-rank operators is Hilbert–Schmidt if the sum
of their norms weighted by the square roots of their ranks is finite. -/
def HilbertSchmidtFiniteRankSeriesStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ι : Type v) (T : ι → (E →L[ℂ] E)) (A : E →L[ℂ] E),
    (∀ j, FiniteDimensional ℂ (T j).toLinearMap.range) →
    Summable (fun j => Real.sqrt (Module.finrank ℂ (T j).toLinearMap.range) * ‖T j‖) →
    HasSum T A → IsHilbertSchmidt A

end Langlands.Analysis.OperatorIdeals
