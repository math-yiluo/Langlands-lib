import Langlands.Representation.RankinSelberg.SymmetricDominant
import Langlands.Representation.RankinSelberg.UnramifiedRecursionUniqueness
import Langlands.Representation.Unramified.PrincipalSeriesHecke
import Mathlib.Order.Interval.Finset.Fin

/-! # The normalized spherical torus recursion -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial
open Langlands.Unramified.MinusculeCosets

/-- The normalized dominant polynomial coefficient on nonnegative torus weights. -/
def sphericalTorusPolynomial {n : ℕ} (q : ℕ) (x : Fin (n + 1) → ℂˣ)
    (α : Fin (n + 1) → ℤ) : ℂ :=
  halfModulus q α * eval (fun i => (x i : ℂ)) (dominantJacobiTrudi ℂ α)

theorem sum_pair_differences {n : ℕ} (α : Fin (n + 1) → ℤ) :
    (∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
      if a < b then α a - α b else 0) =
      ∑ a : Fin (n + 1), ((n : ℤ) - 2 * (a : ℤ)) * α a := by
  have hIoi (a : Fin (n + 1)) :
      (Finset.univ : Finset (Fin (n + 1))).filter (fun b => a < b) = Finset.Ioi a := by
    ext b
    simp
  have hIio (b : Fin (n + 1)) :
      (Finset.univ : Finset (Fin (n + 1))).filter (fun a => a < b) = Finset.Iio b := by
    ext a
    simp
  have hleft :
      (∑ a : Fin (n + 1), ∑ b : Fin (n + 1), if a < b then α a else 0) =
        ∑ a : Fin (n + 1), ((n : ℤ) - a) * α a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_filter, hIoi]
    simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
    have he : (((n + 1 - 1 - a.val : ℕ) : ℤ)) = (n : ℤ) - a := by
      have := a.isLt
      omega
    rw [he]
  have hright :
      (∑ a : Fin (n + 1), ∑ b : Fin (n + 1), if a < b then α b else 0) =
        ∑ b : Fin (n + 1), (b : ℤ) * α b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_filter, hIio]
    simp
  have hpoint (a b : Fin (n + 1)) :
      (if a < b then α a - α b else 0) =
        (if a < b then α a else 0) - (if a < b then α b else 0) := by
    split_ifs <;> ring
  simp_rw [hpoint, Finset.sum_sub_distrib]
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem radical_halfModulus_exponent {n : ℕ} (S : Finset (Fin (n + 1))) :
    2 * (Fintype.card (RadicalPairs S) : ℤ) -
      (∑ a : Fin (n + 1), ((n : ℤ) - 2 * (a : ℤ)) * subsetExponent S a) =
      (S.card * (n + 1 - S.card) : ℕ) := by
  have hN : (Fintype.card (RadicalPairs S) : ℤ) =
      ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        if a ∈ S ∧ b ∉ S ∧ a < b then (1 : ℤ) else 0 := by
    exact_mod_cast Langlands.Unramified.card_radicalPairs S
  have htotal :
      (∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        if a ∈ S ∧ b ∉ S ∧ a < b then (1 : ℤ) else 0) +
      (∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        if a ∉ S ∧ b ∈ S ∧ a < b then (1 : ℤ) else 0) =
      (S.card * (n + 1 - S.card) : ℕ) := by
    exact_mod_cast Langlands.Unramified.separated_pair_count S
  have hpoint (a b : Fin (n + 1)) :
      (if a < b then subsetExponent S a - subsetExponent S b else 0) =
        (if a ∈ S ∧ b ∉ S ∧ a < b then (1 : ℤ) else 0) -
        (if a ∉ S ∧ b ∈ S ∧ a < b then (1 : ℤ) else 0) := by
    by_cases hab : a < b <;> by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
      simp [subsetExponent, hab, ha, hb]
  have hw := sum_pair_differences (subsetExponent S)
  simp_rw [hpoint, Finset.sum_sub_distrib] at hw
  omega

theorem halfModulus_add {n : ℕ} (q : ℕ) (hq : 0 < q)
    (α β : Fin (n + 1) → ℤ) :
    halfModulus q (α + β) = halfModulus q α * halfModulus q β := by
  have hs : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hq)).ne'
  unfold halfModulus
  have he :
      (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * (α + β) i) =
        (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * α i) +
        (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * β i) := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  rw [he, zpow_add₀ hs]

/-- The radical count and half modulus give the standard positive Hecke factor. -/
theorem radical_mul_halfModulus {n : ℕ} (q : ℕ) (hq : 0 < q)
    (S : Finset (Fin (n + 1))) :
    (q : ℂ) ^ Fintype.card (RadicalPairs S) * halfModulus q (subsetExponent S) =
      (Real.sqrt (q : ℝ) : ℂ) ^ (S.card * (n + 1 - S.card)) := by
  let b : ℂ := Real.sqrt (q : ℝ)
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hq)).ne'
  have hsq : b ^ 2 = (q : ℂ) := by
    dsimp [b]
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg q)
  calc
    _ = b ^ (((2 * Fintype.card (RadicalPairs S) : ℕ) : ℤ)) *
        b ^ (-∑ a : Fin (n + 1), ((n : ℤ) - 2 * (a : ℤ)) * subsetExponent S a) := by
      rw [zpow_natCast, pow_mul, hsq]
      rfl
    _ = b ^ ((S.card * (n + 1 - S.card) : ℕ) : ℤ) := by
      rw [← zpow_add₀ hb]
      congr 1
      push_cast
      simpa [sub_eq_add_neg] using radical_halfModulus_exponent S
    _ = _ := by rw [zpow_natCast]

theorem sum_powersetCard_eq_sum_card {m : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Finset (Fin m) → A) (k : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard k, f S) =
      ∑ S : {S : Finset (Fin m) // S.card = k}, f S.val := by
  exact Finset.sum_subtype _ (fun S => by simp) f

theorem eval_esymm_eq_elementaryCoefficient {m : ℕ} (x : Fin m → ℂˣ) (k : ℕ) :
    eval (fun i => (x i : ℂ)) (esymm (Fin m) ℂ k) =
      Langlands.Unramified.elementaryCoefficient (Langlands.Unramified.Eigenvalues.ofTuple x) k := by
  rw [Langlands.Unramified.elementaryCoefficient_ofTuple]
  simp only [esymm, map_sum, map_prod, eval_X]
  exact sum_powersetCard_eq_sum_card _ _

theorem sphericalTorusPolynomial_zero (n q : ℕ) (x : Fin (n + 1) → ℂˣ) :
    sphericalTorusPolynomial q x 0 = 1 := by
  have h0 : Antitone (0 : Fin (n + 1) → ℤ) := fun _ _ _ => le_rfl
  simp [sphericalTorusPolynomial, dominantJacobiTrudi, h0,
    jacobiTrudi_zero, halfModulus_zero]

theorem sphericalTorusPolynomial_eq_zero {n : ℕ} (q : ℕ) (x : Fin (n + 1) → ℂˣ)
    (α : Fin (n + 1) → ℤ) (hα : ¬ Antitone α) :
    sphericalTorusPolynomial q x α = 0 := by
  simp [sphericalTorusPolynomial, dominantJacobiTrudi, hα]

theorem sphericalTorusPolynomial_eq_schur {n : ℕ} (q : ℕ) (x : Fin (n + 1) → ℂˣ)
    (α : Fin (n + 1) → ℤ) (hα : Antitone α) (hpos : ∀ i, 0 ≤ α i) :
    sphericalTorusPolynomial q x α = halfModulus q α * satakeSchur x α := by
  rw [sphericalTorusPolynomial, dominantJacobiTrudi, ite_eq_left hα,
    satakeSchur_eq_eval_jacobiTrudi x α hα hpos]

/-- The exact minuscule recurrence with the radical multiplicities. -/
theorem sphericalTorusPolynomial_recursion {n : ℕ} (q : ℕ) (hq : 0 < q)
    (x : Fin (n + 1) → ℂˣ) (α : Fin (n + 1) → ℤ)
    (hα : Antitone α) (hpos : ∀ i, 0 ≤ α i) (k : ℕ) :
    ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
      Langlands.Unramified.elementaryCoefficient (Langlands.Unramified.Eigenvalues.ofTuple x) k) *
        sphericalTorusPolynomial q x α =
      ∑ S : {S : Finset (Fin (n + 1)) // S.card = k},
        (q : ℂ) ^ Fintype.card (RadicalPairs S.val) *
          sphericalTorusPolynomial q x (α + subsetExponent S.val) := by
  have hPieri := congrArg (eval (fun i => (x i : ℂ)))
    (dominantJacobiTrudi_mul_esymm (R := ℂ) α hα hpos k)
  simp only [map_mul, map_sum] at hPieri
  rw [sum_powersetCard_eq_sum_card] at hPieri
  have hraise (S : Finset (Fin (n + 1))) :
      raiseWeight α S = α + subsetExponent S := rfl
  simp_rw [hraise] at hPieri
  rw [eval_esymm_eq_elementaryCoefficient] at hPieri
  have hterm (S : {S : Finset (Fin (n + 1)) // S.card = k}) :
      (q : ℂ) ^ Fintype.card (RadicalPairs S.val) *
          sphericalTorusPolynomial q x (α + subsetExponent S.val) =
        ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) * halfModulus q α) *
          eval (fun i => (x i : ℂ)) (dominantJacobiTrudi ℂ (α + subsetExponent S.val)) := by
    rw [sphericalTorusPolynomial, halfModulus_add q hq]
    calc
      _ = ((q : ℂ) ^ Fintype.card (RadicalPairs S.val) *
          halfModulus q (subsetExponent S.val)) * halfModulus q α *
          eval (fun i => (x i : ℂ)) (dominantJacobiTrudi ℂ (α + subsetExponent S.val)) := by ring
      _ = _ := by rw [radical_mul_halfModulus q hq, S.property]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← hPieri]
  unfold sphericalTorusPolynomial
  ring

end Langlands.GeneralLinear.Spherical
