import Langlands.Representation.Archimedean.RealTailMultiplierPolynomial
import Langlands.Representation.Archimedean.RealBlockFrobeniusMap
import Langlands.Representation.Archimedean.RealStandardFiltration

/-! # Reciprocal polynomial multipliers on integral generic parity classes -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealIntegralGenericPolynomial

open Polynomial RealBlockMultiplier RealTailMultiplierPolynomial
open Langlands.LocalFactor.Archimedean

theorem pochhammer_shift (n : ℕ) (z : ℂ) :
    (z + 1 - n) * (descPochhammer ℂ n).eval (z + 1) =
      (z + 1) * (descPochhammer ℂ n).eval z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, descPochhammer_succ_eval]
    push_cast
    linear_combination (z - n) * ih

theorem polynomial_recurrence (ℓ : ℕ) (z : ℂ) :
    (tailPolynomial ℓ).eval (z + 2) * (1 - (ℓ : ℂ) + z) =
      (z + 1 + (ℓ : ℂ)) * (tailPolynomial ℓ).eval z := by
  rw [tailPolynomial_eval, tailPolynomial_eval]
  have hh := pochhammer_shift ℓ ((z + (ℓ : ℂ) - 1) / 2)
  have he : (z + 2 + (ℓ : ℂ) - 1) / 2 = (z + (ℓ : ℂ) - 1) / 2 + 1 := by ring
  rw [he]
  linear_combination 2 / (ℓ.factorial : ℂ) * hh

theorem polynomial_ne_zero {ℓ : ℕ} {j : ℤ} (hj : Even (j - (ℓ : ℤ))) :
    (tailPolynomial ℓ).eval (j : ℂ) ≠ 0 := by
  rw [tailPolynomial_eval]
  apply div_ne_zero _ (by exact_mod_cast ℓ.factorial_ne_zero)
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr he
  have hc : (j : ℂ) + (ℓ : ℂ) - 1 = 2 * (r : ℂ) := by
    linear_combination 2 * he
  have hi : j + (ℓ : ℤ) - 1 = 2 * (r : ℤ) := by exact_mod_cast hc
  rw [Int.even_iff] at hj
  omega

theorem polynomial_recurrent (ℓ : ℕ) (ε : ℤ) :
    IsRecurrent (1 - (ℓ : ℂ)) ε (fun j => (tailPolynomial ℓ).eval (j : ℂ)) := by
  intro j _
  convert polynomial_recurrence ℓ (j : ℂ) using 1 <;> push_cast <;> ring

theorem polynomial_symmetric (ℓ : ℕ) (ε : ℤ) :
    IsSymmetric ε ((-1 : ℂ) ^ ℓ) (fun j => (tailPolynomial ℓ).eval (j : ℂ)) := by
  intro j _
  simpa only [Int.cast_neg] using tailPolynomial_neg ℓ (j : ℂ)

def multiplier (ℓ : ℕ) (j : ℤ) : ℂ :=
  ((tailPolynomial ℓ).eval (j : ℂ))⁻¹

theorem multiplier_ne_zero {ℓ : ℕ} {ε j : ℤ}
    (hpar : Even ((ℓ : ℤ) - ε)) (hj : Even (j - ε)) :
    multiplier ℓ j ≠ 0 := by
  apply inv_ne_zero
  apply polynomial_ne_zero
  rw [Int.even_iff] at hpar hj ⊢
  omega

theorem multiplier_recurrent {ℓ : ℕ} {ε : ℤ}
    (hpar : Even ((ℓ : ℤ) - ε)) :
    IsRecurrent ((ℓ : ℂ) + 1) ε (multiplier ℓ) := by
  have hh := (polynomial_recurrent ℓ ε).inv fun j hj => by
    apply polynomial_ne_zero
    rw [Int.even_iff] at hpar hj ⊢
    omega
  convert hh using 1 <;> first | rfl | ring

theorem multiplier_symmetric (ℓ : ℕ) (ε : ℤ) :
    IsSymmetric ε ((-1 : ℂ) ^ ℓ) (multiplier ℓ) := by
  have hs : ((-1 : ℂ) ^ ℓ)⁻¹ = (-1 : ℂ) ^ ℓ := by
    rw [← inv_pow]
    norm_num
  intro j _
  change ((tailPolynomial ℓ).eval ((-j : ℤ) : ℂ))⁻¹ =
    (-1 : ℂ) ^ ℓ * ((tailPolynomial ℓ).eval (j : ℂ))⁻¹
  rw [Int.cast_neg, tailPolynomial_neg, mul_inv, hs]

theorem genericSeq_mul_polynomial {ℓ : ℕ} {ε : ℤ}
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (m : ℕ) :
    genericSeq (ℓ : ℂ) ε m *
        (tailPolynomial ℓ).eval ((ε : ℂ) + 2 * m) =
      (tailPolynomial ℓ).eval (ε : ℂ) := by
  have hν : 0 < ((ℓ : ℂ)).re := by
    simpa only [Complex.natCast_re] using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)
  induction m with
  | zero => simp [genericSeq]
  | succ m ih =>
    have hg := genericSeq_succ hν hε m
    have hp := polynomial_recurrence ℓ ((ε : ℂ) + 2 * m)
    have ha : (ℓ : ℂ) + 1 + ε + 2 * m ≠ 0 := by
      convert genericSeq_denom_ne_zero hν hε m using 1
      ring
    have he : (ε : ℂ) + 2 * (m + 1 : ℕ) = ((ε : ℂ) + 2 * m) + 2 := by
      push_cast
      ring
    rw [he]
    have hh :
        genericSeq (ℓ : ℂ) ε (m + 1) *
            (tailPolynomial ℓ).eval (((ε : ℂ) + 2 * m) + 2) =
          genericSeq (ℓ : ℂ) ε m *
            (tailPolynomial ℓ).eval ((ε : ℂ) + 2 * m) := by
      apply mul_right_cancel₀ ha
      linear_combination
        (tailPolynomial ℓ).eval (((ε : ℂ) + 2 * m) + 2) * hg +
          genericSeq (ℓ : ℂ) ε m * hp
    exact hh.trans ih

theorem genericMultiplier_mul_polynomial_of_nonneg {ℓ : ℕ} {ε j : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hj : 0 ≤ j) (hje : Even (j - ε)) :
    genericMultiplier (ℓ : ℂ) ε j * (tailPolynomial ℓ).eval (j : ℂ) =
      (tailPolynomial ℓ).eval (ε : ℂ) := by
  have hja : (j.natAbs : ℤ) = j := by rw [Int.natCast_natAbs, abs_of_nonneg hj]
  have hi : ε + 2 * ((j.natAbs / 2 : ℕ) : ℤ) = j := by
    rw [Int.even_iff] at hje
    omega
  have hc : (ε : ℂ) + 2 * (j.natAbs / 2 : ℕ) = (j : ℂ) := by
    have hh := congrArg (fun z : ℤ => (z : ℂ)) hi
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hh
  rw [genericMultiplier, extend_of_nonneg hj]
  simpa only [hc] using genericSeq_mul_polynomial hℓ (by omega : 0 ≤ ε) (j.natAbs / 2)

theorem parity_sign {ℓ : ℕ} {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - ε)) :
    (-1 : ℂ) ^ ℓ = (-1 : ℂ) ^ ε.natAbs := by
  have hc : (ε.natAbs : ℤ) = ε := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ ε)]
  have he : ℓ % 2 = ε.natAbs % 2 := by
    rw [Int.even_iff] at hpar
    omega
  exact (neg_one_pow_eq_pow_mod_two (n := ℓ)).trans
    ((congrArg (fun r => (-1 : ℂ) ^ r) he).trans
      (neg_one_pow_eq_pow_mod_two (n := ε.natAbs)).symm)

theorem genericMultiplier_mul_polynomial {ℓ : ℕ} {ε j : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - ε)) (hje : Even (j - ε)) :
    genericMultiplier (ℓ : ℂ) ε j * (tailPolynomial ℓ).eval (j : ℂ) =
      (tailPolynomial ℓ).eval (ε : ℂ) := by
  by_cases hj : 0 ≤ j
  · exact genericMultiplier_mul_polynomial_of_nonneg hℓ hε hj hje
  · have hneg : 0 ≤ -j := by omega
    have he : Even (-j - ε) := by
      rw [Int.even_iff] at hje ⊢
      omega
    have hh := genericMultiplier_mul_polynomial_of_nonneg hℓ hε hneg he
    rw [isSymmetric_genericMultiplier (ℓ : ℂ) hε j hje, Int.cast_neg,
      tailPolynomial_neg, parity_sign hε hpar] at hh
    have hσ := neg_one_pow_sq ε.natAbs
    calc
      genericMultiplier (ℓ : ℂ) ε j * (tailPolynomial ℓ).eval (j : ℂ) =
          ((-1 : ℂ) ^ ε.natAbs) ^ 2 *
            (genericMultiplier (ℓ : ℂ) ε j * (tailPolynomial ℓ).eval (j : ℂ)) := by rw [hσ, one_mul]
      _ = (tailPolynomial ℓ).eval (ε : ℂ) := by
        convert hh using 1
        ring

/-- The existing normalized integral generic multiplier is an explicit reciprocal polynomial. -/
theorem genericMultiplier_eq {ℓ : ℕ} {ε j : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - ε)) (hje : Even (j - ε)) :
    genericMultiplier (ℓ : ℂ) ε j =
      (tailPolynomial ℓ).eval (ε : ℂ) / (tailPolynomial ℓ).eval (j : ℂ) := by
  apply (eq_div_iff (polynomial_ne_zero (by
    rw [Int.even_iff] at hpar hje ⊢
    omega))).mpr
  exact genericMultiplier_mul_polynomial hℓ hε hpar hje

open RealStandardFiltration RealBlockFrobeniusMap RealBlockJacquet in
/-- The normalized generic Frobenius map obeys a polynomial Fourier relation. -/
theorem generic_frob_relation {n p ℓ : ℕ} {ds es : List RealBlock} {ε : ℤ} {τ : ℂ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - ε))
    (hdata : IsBlockFrobData n ds es p ε τ (genericMultiplier (ℓ : ℂ) ε))
    (f : KF n ds) (j : ℤ) {g : Langlands.GeneralLinear n ℝ}
    (hg : g ∈ unitaryCompact ℝ n) :
    (tailPolynomial ℓ).eval (j : ℂ) *
        blockFourierCoefficient n p j (blockFrobMap hdata f) g =
      (tailPolynomial ℓ).eval (ε : ℂ) * blockFourierCoefficient n p j f g := by
  rw [blockFourierCoefficient_blockFrobMap hdata f hg]
  by_cases he : Even (j - ε)
  · calc
      (tailPolynomial ℓ).eval (j : ℂ) *
          (genericMultiplier (ℓ : ℂ) ε j * blockFourierCoefficient n p j f g) =
        (genericMultiplier (ℓ : ℂ) ε j * (tailPolynomial ℓ).eval (j : ℂ)) *
          blockFourierCoefficient n p j f g := by ring
      _ = _ := by rw [genericMultiplier_mul_polynomial hℓ hε hpar he]
  · rw [blockFourierCoefficient_eq_zero_of_not_even hdata.lt hdata.par f he g,
      mul_zero, mul_zero, mul_zero]

end Langlands.Archimedean.RealIntegralGenericPolynomial

namespace Langlands.Archimedean

open RealBlockMultiplier RealTailMultiplierPolynomial RealIntegralGenericPolynomial in
/-- Normalized integral generic multipliers are reciprocal differential-tail polynomials. -/
def RealIntegralGenericPolynomialStatement : Prop :=
  ∀ (ℓ : ℕ) (ε : ℤ), 0 < ℓ → (ε = 0 ∨ ε = 1) → Even ((ℓ : ℤ) - ε) →
    (tailPolynomial ℓ).eval (ε : ℂ) ≠ 0 ∧
      IsRecurrent ((ℓ : ℂ) + 1) ε (multiplier ℓ) ∧
      IsSymmetric ε ((-1 : ℂ) ^ ℓ) (multiplier ℓ) ∧
      ∀ j : ℤ, Even (j - ε) →
        multiplier ℓ j ≠ 0 ∧ genericMultiplier (ℓ : ℂ) ε j =
          (tailPolynomial ℓ).eval (ε : ℂ) / (tailPolynomial ℓ).eval (j : ℂ)

theorem realIntegralGenericPolynomial : RealIntegralGenericPolynomialStatement := by
  intro ℓ ε hℓ hε hpar
  refine ⟨RealIntegralGenericPolynomial.polynomial_ne_zero ?_,
    RealIntegralGenericPolynomial.multiplier_recurrent hpar,
    RealIntegralGenericPolynomial.multiplier_symmetric ℓ ε, ?_⟩
  · rw [Int.even_iff] at hpar ⊢
    omega
  · intro j hj
    exact ⟨RealIntegralGenericPolynomial.multiplier_ne_zero hpar hj,
      RealIntegralGenericPolynomial.genericMultiplier_eq hℓ hε hpar hj⟩

end Langlands.Archimedean
