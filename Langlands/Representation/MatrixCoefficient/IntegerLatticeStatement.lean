import Langlands.Representation.MatrixCoefficient.Definitions
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Exponential-polynomial matrix coefficients on the integer lattice -/

namespace Langlands

universe u

/-- Renard C.III: every coefficient of a finite-dimensional complex lattice
representation is one finite sum of characters times polynomials on the whole
integer lattice. This declaration states the proposition. -/
def IntegerLatticeMatrixCoefficientExponentialPolynomialStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin d → ℤ)) V)
    (v : V) (ell : Module.Dual ℂ V),
    ∃ (l : ℕ) (χ : Fin l → Multiplicative (Fin d → ℤ) →* ℂˣ)
      (Q : Fin l → MvPolynomial (Fin d) ℂ),
      ∀ n : Fin d → ℤ,
        matrixCoefficient ρ ell v (Multiplicative.ofAdd n) =
          ∑ j, (χ j (Multiplicative.ofAdd n) : ℂ) *
            MvPolynomial.eval (fun i => (n i : ℂ)) (Q j)

end Langlands
