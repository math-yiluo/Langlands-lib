import Mathlib.Algebra.Star.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-! # Lifting an idempotent whose adjoint is its complement -/

namespace Langlands.Algebra

/-- An idempotent whose adjoint is its complement lifts through a square-zero
kernel of a surjective involution-preserving rational algebra map. -/
theorem exists_lift_idempotent_star_eq_one_sub
    {R S : Type*} [Ring R] [Ring S] [StarRing R] [StarRing S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (hf : Function.Surjective f) (hstar : ∀ x, f (star x) = star (f x))
    (hker : ∀ x, f x = 0 → x ^ 2 = 0)
    (e : S) (he : IsIdempotentElem e) (heStar : star e = 1 - e) :
    ∃ p : R, IsIdempotentElem p ∧ f p = e ∧ star p = 1 - p := by
  obtain ⟨x, hx⟩ := hf e
  let q : R := (1 / 2 : ℚ) • (x + (1 - star x))
  have hq : f q = e := by
    have hsum : e + (1 - (1 - e)) = (2 : ℚ) • e := by
      rw [two_smul]
      abel
    rw [show f q = (1 / 2 : ℚ) • (e + (1 - (1 - e))) by
      simp only [q, map_smul, map_add, map_sub, map_one, hstar, hx, heStar],
      hsum, smul_smul]
    norm_num
  have hqStar : star q = 1 - q := by
    apply eq_sub_of_add_eq
    simp only [q, star_rat_smul, star_add, star_sub, star_one, star_star, ← smul_add]
    have hsum : (star x + (1 - x)) + (x + (1 - star x)) = (2 : ℚ) • (1 : R) := by
      rw [two_smul]
      abel
    rw [hsum, smul_smul]
    norm_num
  have he₂ : e ^ 2 = e := by rw [pow_two]; exact he
  have hq₂ : (q ^ 2 - q) ^ 2 = 0 :=
    hker _ (by rw [map_sub, map_pow, hq, he₂, sub_self])
  let p : R := 3 * q ^ 2 - 2 * q ^ 3
  have hp : p * p - p = (q ^ 2 - q) ^ 2 * (4 * q ^ 2 - 4 * q - 3) := by
    dsimp only [p]
    noncomm_ring
  refine ⟨p, sub_eq_zero.mp (hp.trans (by rw [hq₂, zero_mul])), ?_, ?_⟩
  · have he₃ : e ^ 3 = e := by rw [pow_succ, he₂]; exact he
    simp only [p, map_sub, map_mul, map_ofNat, map_pow, hq, he₂, he₃]
    noncomm_ring
  · simp only [p, star_sub, star_mul, star_pow, star_ofNat, hqStar]
    noncomm_ring

end Langlands.Algebra
