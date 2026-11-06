import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Ring.Parity

/-! # Coxeter relations from conjugacy of involutive lifts -/

universe u v w x

namespace Langlands.Group.CoxeterLift

variable {Q : Type u} [Group Q]

/-- Conjugating one of two involutions by a power of their product doubles the power. -/
theorem conjugate_pow (A B : Q) (hA : A * A = 1) (hB : B * B = 1) (k : ℕ) :
    (A * B) ^ k * A * ((A * B) ^ k)⁻¹ = (A * B) ^ (2 * k) * A := by
  have hiA : A⁻¹ = A := (eq_inv_of_mul_eq_one_right hA).symm
  have hiB : B⁻¹ = B := (eq_inv_of_mul_eq_one_right hB).symm
  have hs : SemiconjBy A (A * B)⁻¹ (A * B) := by
    change A * (A * B)⁻¹ = (A * B) * A
    simp only [mul_inv_rev, hiA, hiB, mul_assoc]
  calc
    _ = (A * B) ^ k * (A * ((A * B)⁻¹) ^ k) := by
      rw [inv_pow, mul_assoc]
    _ = (A * B) ^ k * ((A * B) ^ k * A) := by rw [hs.pow_right k]
    _ = (A * B) ^ (2 * k) * A := by rw [← mul_assoc, ← pow_add, two_mul]

/-- The even power relation is equivalent to fixing the first involution by conjugacy. -/
theorem conjugate_pow_eq_left_iff (A B : Q) (hA : A * A = 1)
    (hB : B * B = 1) (k : ℕ) :
    (A * B) ^ k * A * ((A * B) ^ k)⁻¹ = A ↔ (A * B) ^ (2 * k) = 1 := by
  rw [conjugate_pow A B hA hB]
  constructor
  · intro h
    have hh := congrArg (· * A) h
    simpa only [mul_assoc, hA, mul_one] using hh
  · intro h
    rw [h, one_mul]

/-- The odd power relation is equivalent to interchanging the two involutions by conjugacy. -/
theorem conjugate_pow_eq_right_iff (A B : Q) (hA : A * A = 1)
    (hB : B * B = 1) (k : ℕ) :
    (A * B) ^ k * A * ((A * B) ^ k)⁻¹ = B ↔ (A * B) ^ (2 * k + 1) = 1 := by
  rw [conjugate_pow A B hA hB]
  constructor
  · intro h
    rw [pow_succ, ← mul_assoc, h, hB]
  · intro h
    calc
      _ = (A * B) ^ (2 * k) * (A * B) * B := by
        simp only [mul_assoc, hB, mul_one]
      _ = B := by rw [← pow_succ, h, one_mul]

variable {B : Type v} {N : Type w} {W : Type x} [Group N] [Group W]
  {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Compatibility of the two homomorphisms with conjugacy between labelled simple lifts. -/
def CompatibleSimpleConjugacy (q : N →* W) (f : N →* Q) (m : B → N) : Prop :=
  ∀ (n : N) (a b : B),
    q n * cs.simple a * (q n)⁻¹ = cs.simple b →
      f n * f (m a) * (f n)⁻¹ = f (m b)

/-- If conjugacy between simple reflections lifts to conjugacy of their involutive
images, then all Coxeter relations hold among those images. -/
theorem isLiftable_of_conjugacy (q : N →* W) (f : N →* Q) (m : B → N)
    (hm : ∀ a, q (m a) = cs.simple a)
    (hinv : ∀ a, f (m a) * f (m a) = 1)
    (hconj : CompatibleSimpleConjugacy cs q f m) :
    M.IsLiftable (fun a => f (m a)) := by
  intro a b
  obtain ⟨k, heven | hodd⟩ := Nat.even_or_odd' (M a b)
  · rw [heven]
    apply (conjugate_pow_eq_left_iff _ _ (hinv a) (hinv b) k).1
    have hc : (cs.simple a * cs.simple b) ^ k * cs.simple a *
        ((cs.simple a * cs.simple b) ^ k)⁻¹ = cs.simple a := by
      apply (conjugate_pow_eq_left_iff _ _
        (cs.simple_mul_simple_self a) (cs.simple_mul_simple_self b) k).2
      simpa only [heven] using cs.simple_mul_simple_pow a b
    have h := hconj ((m a * m b) ^ k) a a (by
      simpa only [map_pow, map_mul, hm] using hc)
    simpa only [map_pow, map_mul] using h
  · rw [hodd]
    apply (conjugate_pow_eq_right_iff _ _ (hinv a) (hinv b) k).1
    have hc : (cs.simple a * cs.simple b) ^ k * cs.simple a *
        ((cs.simple a * cs.simple b) ^ k)⁻¹ = cs.simple b := by
      apply (conjugate_pow_eq_right_iff _ _
        (cs.simple_mul_simple_self a) (cs.simple_mul_simple_self b) k).2
      simpa only [hodd] using cs.simple_mul_simple_pow a b
    have h := hconj ((m a * m b) ^ k) a b (by
      simpa only [map_pow, map_mul, hm] using hc)
    simpa only [map_pow, map_mul] using h

end Langlands.Group.CoxeterLift
