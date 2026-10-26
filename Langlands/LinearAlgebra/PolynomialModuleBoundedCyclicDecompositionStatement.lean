import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Bounded cyclic decomposition of an annihilated polynomial module

This module states an internal algebraic prerequisite for finiteness of matrix
conjugacy classes with fixed characteristic polynomial. It supplies no proof.
-/

namespace Langlands

universe uK uV

/-- A finite-dimensional polynomial module annihilated by a nonzero polynomial
is a product of at most its vector-space dimension many cyclic quotients whose
monic defining polynomials divide the annihilating polynomial. -/
def PolynomialModuleBoundedCyclicDecompositionStatement : Prop :=
  ∀ (K : Type uK) [Field K] (V : Type uV)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) (c : Polynomial K),
    c ≠ 0 → Polynomial.aeval f c = 0 →
      ∃ (m : ℕ) (q : Fin m → Polynomial K),
        m ≤ Module.finrank K V ∧
          (∀ i, (q i).Monic ∧ q i ∣ c) ∧
          Nonempty (Module.AEval' f ≃ₗ[Polynomial K]
            ((i : Fin m) → Polynomial K ⧸ Ideal.span ({q i} : Set (Polynomial K))))

end Langlands
