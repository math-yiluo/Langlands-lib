import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Polynomial roots of invertible complex endomorphisms

This module states the polynomial-root existence property used in
Henniart's unramified reduction argument.
-/

namespace Langlands

universe u

/-- Every invertible endomorphism of a finite-dimensional complex vector space
has a polynomial nth root for every positive natural n, including on the
zero-dimensional vector space. -/
def ComplexPolynomialRoots : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : Module.End ℂ V), IsUnit A →
    ∀ n : ℕ, 0 < n →
      ∃ p : Polynomial ℂ, (Polynomial.aeval A p) ^ n = A

end Langlands
