import Langlands.Global.IntegralFiniteAdeles
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Rationalization of the integral finite adeles of the rationals -/

open scoped TensorProduct

namespace Langlands.Global

/-- The algebraic rationalization `ℚ ⊗[ℤ] integralFiniteAdeles ℚ` of the actual
integral finite adeles identifies, as a `ℚ`-algebra, with the existing finite
adele ring of `ℚ`, by `q ⊗ a ↦ q · a`. This is a theorem statement, not a
supplied or chosen equivalence. -/
def IntegralFiniteAdeleRationalization : Prop :=
  ∃ E : (ℚ ⊗[ℤ] integralFiniteAdeles ℚ) ≃ₐ[ℚ] FiniteAdeles ℚ,
    ∀ (q : ℚ) (a : integralFiniteAdeles ℚ),
      E (q ⊗ₜ[ℤ] a) = algebraMap ℚ (FiniteAdeles ℚ) q * (a : FiniteAdeles ℚ)

end Langlands.Global
