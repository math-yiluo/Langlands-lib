import Langlands.Cohomology.Weights.Separation

/-!
# The alternating characteristic function concentrated in one degree

If all characteristic polynomials but the one in degree `k` are `1`, the alternating
characteristic rational function is that polynomial to the power `(-1)^k`. If it equals
`P^a` for a monic polynomial `P` of positive degree, the polynomial in degree `k` is
`P^{|a|}`. This is the algebra by which Kottwitz (1992), printed p. 658, passes from
his identity for the alternating sum to one degree when the cohomology lies in one
degree; no weight argument is used.
-/

noncomputable section

open Polynomial
open scoped BigOperators

universe u

namespace Langlands.Cohomology.Weights

variable {L : Type u} [Field L]

/-- With all polynomials outside degree `k` equal to `1`, the alternating
characteristic rational function is the polynomial of degree `k` to the power
`(-1)^k`. -/
theorem alternatingPolynomial_eq_of_eq_one {d : ℕ} (H : Fin (2 * d + 1) → L[X])
    (k : Fin (2 * d + 1)) (hH : ∀ i, i ≠ k → H i = 1) :
    alternatingPolynomial d H =
      (algebraMap L[X] (RatFunc L) (H k)) ^ ((-1 : ℤ) ^ k.val) := by
  unfold alternatingPolynomial
  rw [Finset.prod_eq_single k]
  · intro i _ hik
    rw [hH i hik, map_one, one_zpow]
  · intro h
    exact (h (Finset.mem_univ k)).elim

/-- A monic polynomial `H` whose image in the field of rational functions satisfies
`H^{±1} = P^a`, for a monic `P` of positive degree, is `P^{|a|}`. -/
theorem eq_pow_natAbs_of_zpow_eq {H P : L[X]} (hH : H.Monic) (hP : P.Monic)
    (hdeg : 0 < P.natDegree) {e a : ℤ} (he : e = 1 ∨ e = -1)
    (h : (algebraMap L[X] (RatFunc L) H) ^ e = (algebraMap L[X] (RatFunc L) P) ^ a) :
    H = P ^ a.natAbs := by
  set x := algebraMap L[X] (RatFunc L) H with hx
  set y := algebraMap L[X] (RatFunc L) P with hy
  have hy0 : y ≠ 0 := by
    rw [hy]
    exact (map_ne_zero_iff _ (IsFractionRing.injective L[X] (RatFunc L))).mpr hP.ne_zero
  -- In both cases `x = y ^ b` with `b = ± a`.
  obtain ⟨b, hb, hxb⟩ : ∃ b : ℤ, b.natAbs = a.natAbs ∧ x = y ^ b := by
    rcases he with rfl | rfl
    · exact ⟨a, rfl, by simpa using h⟩
    · refine ⟨-a, Int.natAbs_neg a, ?_⟩
      have h' : x⁻¹ = y ^ a := by simpa using h
      rw [zpow_neg, ← h', inv_inv]
  have inj := IsFractionRing.injective L[X] (RatFunc L)
  rcases le_or_gt 0 b with hb0 | hb0
  · -- `b ≥ 0`: the identity is an identity of polynomials.
    have hbn : b = (b.natAbs : ℤ) := (Int.natAbs_of_nonneg hb0).symm
    rw [hbn, zpow_natCast, hy, ← map_pow] at hxb
    rw [← hb]
    exact inj hxb
  · -- `b < 0`: then `H · P^{|b|} = 1`, impossible for degree reasons.
    exfalso
    have hbn : b = -(b.natAbs : ℤ) := by omega
    rw [hbn, zpow_neg, zpow_natCast] at hxb
    have hprod : x * y ^ b.natAbs = 1 := by
      rw [hxb, inv_mul_cancel₀ (pow_ne_zero _ hy0)]
    rw [hx, hy, ← map_pow, ← map_mul] at hprod
    have hpoly : H * P ^ b.natAbs = 1 := inj (by rw [hprod, map_one])
    have hdeg' := congrArg Polynomial.natDegree hpoly
    rw [natDegree_mul hH.ne_zero (pow_ne_zero _ hP.ne_zero), natDegree_pow,
      natDegree_one] at hdeg'
    have hpos : 0 < b.natAbs := Int.natAbs_pos.mpr (by omega)
    have : 0 < b.natAbs * P.natDegree := Nat.mul_pos hpos hdeg
    omega

/-- Concentration in one degree: if all polynomials outside degree `k` are `1` and
the alternating characteristic rational function is `P^a` for a monic `P` of positive
degree, then the monic polynomial of degree `k` is `P^{|a|}`. -/
theorem eq_pow_natAbs_of_alternating {d : ℕ} (H : Fin (2 * d + 1) → L[X])
    (k : Fin (2 * d + 1)) (hH : ∀ i, i ≠ k → H i = 1) (hk : (H k).Monic)
    {P : L[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {a : ℤ}
    (h : alternatingPolynomial d H = (algebraMap L[X] (RatFunc L) P) ^ a) :
    H k = P ^ a.natAbs := by
  rw [alternatingPolynomial_eq_of_eq_one H k hH] at h
  exact eq_pow_natAbs_of_zpow_eq hk hP hdeg (neg_one_pow_eq_or ℤ k.val) h

/-- Under the same hypotheses the polynomial of degree `k` has positive degree exactly
when `a ≠ 0`. -/
theorem natDegree_pos_iff_of_alternating {d : ℕ} (H : Fin (2 * d + 1) → L[X])
    (k : Fin (2 * d + 1)) (hH : ∀ i, i ≠ k → H i = 1) (hk : (H k).Monic)
    {P : L[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {a : ℤ}
    (h : alternatingPolynomial d H = (algebraMap L[X] (RatFunc L) P) ^ a) :
    0 < (H k).natDegree ↔ a ≠ 0 := by
  rw [eq_pow_natAbs_of_alternating H k hH hk hP hdeg h, natDegree_pow]
  constructor
  · intro hpos ha
    rw [ha] at hpos
    simp at hpos
  · intro ha
    exact Nat.mul_pos (Int.natAbs_pos.mpr ha) hdeg

end Langlands.Cohomology.Weights
