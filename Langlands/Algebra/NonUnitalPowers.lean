import Mathlib.Algebra.Algebra.Unitization
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Positive products, nilpotence and actual unitization comparisons

Renard (9 July 2026), Appendix B.II and B.III, printed pp. 272–273: both proofs replace a
possibly nonunital complex algebra `A` by its unitization `A ⊕ ℂ 1_A`. This module supplies
elementary algebraic and dimension details of that reduction, using Mathlib's actual
`Unitization k A` and its embedding `Unitization.inr`. The definitions and comparison laws are
derived implementation content, not numbered results of the source.

`successorPower a n` is the product of `n + 1` copies of `a`, and `IsNonUnitalNilpotent a`
says that one such positive product vanishes. Neither introduces a multiplicative identity or
a natural-power instance on the original carrier.
-/

universe uK uA uB

namespace Langlands.Algebra

/-- The product of `n + 1` copies of `a`, associated on the left, without requiring a
multiplicative identity: index zero is `a`, and the successor multiplies on the right by `a`. -/
def successorPower {A : Type uA} [Mul A] (a : A) : ℕ → A
  | 0 => a
  | n + 1 => successorPower a n * a

/-- Nilpotence expressed by vanishing of a positive product in the original carrier. -/
def IsNonUnitalNilpotent {A : Type uA} [Mul A] [Zero A] (a : A) : Prop :=
  ∃ n : ℕ, successorPower a n = 0

@[simp] theorem successorPower_zero {A : Type uA} [Mul A] (a : A) :
    successorPower a 0 = a := rfl

@[simp] theorem successorPower_succ {A : Type uA} [Mul A] (a : A) (n : ℕ) :
    successorPower a (n + 1) = successorPower a n * a := rfl

/-- In a monoid, the positive product of `n + 1` copies of `a` is `a ^ (n + 1)`. -/
theorem successorPower_eq_pow {A : Type uA} [Monoid A] (a : A) (n : ℕ) :
    successorPower a n = a ^ (n + 1) := by
  induction n with
  | zero => simp [successorPower]
  | succ n ih => simp only [successorPower, ih, pow_succ]

/-- In a monoid with zero, nonunital nilpotence is ordinary `IsNilpotent`. -/
theorem isNonUnitalNilpotent_iff {A : Type uA} [MonoidWithZero A] (a : A) :
    IsNonUnitalNilpotent a ↔ IsNilpotent a := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, (successorPower_eq_pow a n).symm.trans hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [successorPower_eq_pow, pow_succ, hn, zero_mul]⟩

/-- An actual nonunital ring homomorphism preserves positive products. -/
theorem map_successorPower {A : Type uA} {B : Type uB}
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] (f : A →ₙ+* B) (a : A) (n : ℕ) :
    f (successorPower a n) = successorPower (f a) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [successorPower, map_mul, ih]

section Unitization

variable (k : Type uK) [CommRing k]
variable {A : Type uA} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The actual embedding `Unitization.inr` sends the positive product of `n + 1` copies of `a`
to the `(n + 1)`st power of the image of `a`. -/
theorem inr_successorPower (a : A) (n : ℕ) :
    (Unitization.inr (successorPower a n) : Unitization k A) =
      (Unitization.inr a : Unitization k A) ^ (n + 1) := by
  induction n with
  | zero => simp [successorPower]
  | succ n ih =>
    rw [successorPower, Unitization.inr_mul, ih]
    exact (pow_succ _ _).symm

/-- The image of `a` in the actual unitization is nilpotent exactly when `a` is nonunitally
nilpotent. -/
theorem isNilpotent_inr_iff (a : A) :
    IsNilpotent (Unitization.inr a : Unitization k A) ↔ IsNonUnitalNilpotent a := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Unitization.inr_injective (R := k) ?_⟩
    rw [inr_successorPower, Unitization.inr_zero, pow_succ, hn, zero_mul]
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by rw [← inr_successorPower, hn, Unitization.inr_zero]⟩

end Unitization

section Rank

variable (k : Type uK) [Field k]
variable (A : Type uA) [AddCommGroup A] [Module k A]

/-- Over a field, the actual unitization has at most countable rank exactly when the original
vector space does. -/
theorem unitization_countableRank_iff :
    Module.rank k (Unitization k A) ≤ Cardinal.aleph0 ↔
      Module.rank k A ≤ Cardinal.aleph0 := by
  rw [(Unitization.linearEquiv k k A).rank_eq, rank_prod]
  simp only [Module.rank_self, Cardinal.lift_one, Cardinal.add_le_aleph0,
    Cardinal.lift_le_aleph0, Cardinal.one_le_aleph0, true_and]

end Rank

end Langlands.Algebra
