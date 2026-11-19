import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Finiteness

/-! # Finite-order detection modulo an integer in a finitely generated abelian group -/

universe u

namespace Langlands

/-- A finite-order additive automorphism of a finitely generated abelian group is
the identity if it is the identity modulo `nM`, where `3 ≤ n` and multiplication
by `n` kills every torsion element. This is the algebraic input in Conrad,
*Reductive group schemes* (2014), proof of Corollary B.3.6, p. 294. Conrad
chooses `n ≥ 3` divisible by the torsion exponent and uses the same bound when
invoking torsion-freeness of the principal congruence kernel in `GL_d(ℤ)`. -/
def FiniteOrderCongruenceDetectionStatement : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (n : ℕ), 3 ≤ n →
    (∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → n • x = 0) →
    ∀ σ : M ≃+ M,
      (∃ r : ℕ, 0 < r ∧ (σ.toEquiv : Equiv.Perm M) ^ r = 1) →
      (∀ x : M, ∃ y : M, σ x = x + n • y) →
      σ = AddEquiv.refl M

end Langlands
