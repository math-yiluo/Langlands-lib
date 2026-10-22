import Langlands.Global.ProfiniteIntegerRing
import Langlands.Global.IntegralFiniteAdeles
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Normalized rational profinite-integer and finite-adele comparison -/

open scoped TensorProduct

namespace Langlands.Global

/-- The residue ring identifies topologically with the actual integral finite
adeles of the rationals, and its rationalization identifies with the existing
finite adele algebra by the prescribed simple-tensor formula. This is a theorem
statement, not a supplied comparison or a chosen equivalence. -/
def RationalProfiniteIntegerAdeleComparison : Prop :=
  ∃ e₀ : ProfiniteIntegerRing ≃+* integralFiniteAdeles ℚ,
    Continuous e₀ ∧ Continuous e₀.symm ∧
      (∀ z : ℤ, (e₀ (ProfiniteIntegerRing.intCastHom z) : FiniteAdeles ℚ) =
        algebraMap ℚ (FiniteAdeles ℚ) (z : ℚ)) ∧
      ∃ e : (ℚ ⊗[ℤ] ProfiniteIntegerRing) ≃ₐ[ℚ] FiniteAdeles ℚ,
        ∀ (q : ℚ) (a : ProfiniteIntegerRing),
          e (q ⊗ₜ[ℤ] a) = algebraMap ℚ (FiniteAdeles ℚ) q *
            (e₀ a : FiniteAdeles ℚ)

end Langlands.Global
