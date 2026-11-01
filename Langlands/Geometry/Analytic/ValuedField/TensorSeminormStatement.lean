import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.RingTheory.TensorProduct.Basic

/-! # A normalized ultrametric seminorm on the tensor product of two valued fields -/

universe u

namespace Langlands.Analytic

open scoped TensorProduct

/-- For complete ultrametric normed fields `F` and `G` that are normed algebras over a
complete ultrametric normed field `E`, the algebraic tensor product `F ⊗[E] G` carries a
nonarchimedean ring seminorm `p` with `p 1 = 1`, `p (a ⊗ₜ 1) ≤ ‖a‖` and `p (1 ⊗ₜ b) ≤ ‖b‖`. -/
def TensorSeminormStatement : Prop :=
  ∀ (E F G : Type u)
    [NormedField E] [IsUltrametricDist E] [CompleteSpace E]
    [NormedField F] [IsUltrametricDist F] [CompleteSpace F] [NormedAlgebra E F]
    [NormedField G] [IsUltrametricDist G] [CompleteSpace G] [NormedAlgebra E G],
    ∃ p : RingSeminorm (F ⊗[E] G), p 1 = 1 ∧ IsNonarchimedean p ∧
      (∀ a : F, p (a ⊗ₜ[E] (1 : G)) ≤ ‖a‖) ∧
      (∀ b : G, p ((1 : F) ⊗ₜ[E] b) ≤ ‖b‖)

end Langlands.Analytic
