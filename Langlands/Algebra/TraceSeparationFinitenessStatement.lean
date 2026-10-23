import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.Basic

/-! A finite-generation and trace-isolation criterion for finiteness. -/

namespace Langlands

universe uA uI

/-- In fixed matrix dimension, a trace-isolated family of representations of a
finitely generated complex algebra has finite index type. -/
def TraceSeparationFinitenessStatement : Prop :=
  ∀ (A : Type uA) [Ring A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (d : ℕ) (I : Type uI)
    (ρ : I → A →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ),
    (∀ i, ∃ a : A, Matrix.trace (ρ i a) ≠ 0 ∧
      ∀ j, j ≠ i → Matrix.trace (ρ j a) = 0) →
    Finite I

end Langlands
