import Langlands.LocalFactor.Euler.Definitions

/-! # Scaling the Euler polynomial of a complex operator -/

noncomputable section

namespace Langlands.Henniart.Extension

open Polynomial

/-- Scaling an operator substitutes `c X` in its Euler polynomial. -/
theorem eulerPolynomial_smul {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (c : ℂ) :
    LocalFactor.eulerPolynomial (c • A) =
      (LocalFactor.eulerPolynomial A).comp (C c * X) := by
  apply Polynomial.funext
  intro x
  rw [LocalFactor.eulerPolynomial_eval, eval_comp, eval_mul, eval_C, eval_X,
    LocalFactor.eulerPolynomial_eval, smul_smul, mul_comm x c]

end Langlands.Henniart.Extension
