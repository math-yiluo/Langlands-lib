import Langlands.LocalFactor.Archimedean.RealTateProof

/-! # Polynomial Gaussians in the real Tate integral -/

noncomputable section

open Complex MeasureTheory Polynomial
open scoped Real SchwartzMap

set_option autoImplicit false

namespace Langlands.LocalFactor.RealTate

/-- A monomial times the Gaussian of scale `π`, as a Schwartz function. -/
def monomialGaussian (m : ℕ) : 𝓢(ℝ, ℂ) := gaussSchwartz (X ^ m)

@[simp]
theorem monomialGaussian_apply (m : ℕ) (x : ℝ) :
    monomialGaussian m x = (x : ℂ) ^ m * exp (-(π : ℂ) * (x : ℂ) ^ 2) := by
  rw [monomialGaussian, gaussSchwartz_apply, eval_pow, eval_X, ofReal_pow]

private theorem reflect_monomialGaussian (m : ℕ) (x : ℝ) :
    reflect (monomialGaussian m) x = (-1 : ℂ) ^ m * monomialGaussian m x := by
  rw [reflect_apply, monomialGaussian_apply, monomialGaussian_apply, ofReal_neg, neg_sq,
    ← neg_one_mul (x : ℂ), mul_pow, mul_assoc]

private theorem mellin_reflect_monomialGaussian (m : ℕ) (u : ℂ) :
    mellin (fun x => reflect (monomialGaussian m) x) u =
      (-1 : ℂ) ^ m * mellin (fun x => monomialGaussian m x) u := by
  simp only [mellin, reflect_monomialGaussian, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext x
  ring

private theorem zeta_monomialGaussian_add_two (m : ℕ) (e : Fin 2) (u : ℂ) :
    zeta (monomialGaussian (m + 2)) e u = zeta (monomialGaussian m) e (u + 2) := by
  unfold zeta
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  have hx' : ((|x| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
  have hsq : ((|x| : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 := by exact_mod_cast sq_abs x
  simp only [integrand, hx, ite_false, monomialGaussian_apply, pow_add]
  rw [show u + 2 - 1 = (u - 1) + (2 : ℕ) by push_cast; ring, cpow_add _ _ hx',
    cpow_natCast, hsq]
  ring

/-- The zeta integral of a real monomial Gaussian is a polynomial multiple of its parity
factor on the right half-plane. -/
theorem zeta_monomialGaussian (m : ℕ) (e : Fin 2) :
    ∃ Q : Polynomial ℂ, ∀ u, 0 < u.re →
      zeta (monomialGaussian m) e u = Q.eval u * Gammaℝ (u + e.val) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    fin_cases e
    · refine ⟨1, fun u hu => ?_⟩
      rw [eval_one, one_mul]
      exact zeta_gaussSchwartzE (⟨0, by decide⟩ : Fin 2) hu
    · refine ⟨0, fun u hu => ?_⟩
      rw [zeta_eq_mellin _ _ hu, mellin_reflect_monomialGaussian]
      norm_num
  | one =>
    fin_cases e
    · refine ⟨0, fun u hu => ?_⟩
      rw [zeta_eq_mellin _ _ hu, mellin_reflect_monomialGaussian]
      norm_num
    · refine ⟨1, fun u hu => ?_⟩
      rw [eval_one, one_mul]
      exact zeta_gaussSchwartzE (⟨1, by decide⟩ : Fin 2) hu
  | more m ih _ =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q.comp (X + C 2) * (X + C (e.val : ℂ)) * C (2 * (π : ℂ))⁻¹, ?_⟩
    intro u hu
    have hshift : 0 < (u + 2).re := by simp only [add_re, re_ofNat]; linarith
    have hne : u + (e.val : ℂ) ≠ 0 := by
      apply ne_of_apply_ne re
      simp only [add_re, natCast_re, zero_re]
      have he : 0 ≤ (e.val : ℝ) := Nat.cast_nonneg _
      linarith
    rw [zeta_monomialGaussian_add_two, hQ _ hshift,
      show u + 2 + (e.val : ℂ) = (u + (e.val : ℂ)) + 2 by ring, Gammaℝ_add_two hne]
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_C, div_eq_mul_inv]
    ring

/-- The Schwartz function represented by a complex polynomial times the Gaussian of scale `π`. -/
def polynomialGaussian (P : Polynomial ℂ) : 𝓢(ℝ, ℂ) :=
  ∑ m ∈ P.support, P.coeff m • monomialGaussian m

@[simp]
theorem polynomialGaussian_apply (P : Polynomial ℂ) (x : ℝ) :
    polynomialGaussian P x = P.eval (x : ℂ) * exp (-(π : ℂ) * (x : ℂ) ^ 2) := by
  simp only [polynomialGaussian, sum_apply, smul_apply, smul_eq_mul,
    monomialGaussian_apply, eval_eq_sum, Polynomial.sum, Finset.sum_mul, mul_assoc]

/-- The real Tate integral of any complex polynomial Gaussian is a polynomial multiple of
`Γℝ(u + e)` on `Re(u) > 0`. -/
def RealTatePolynomialGaussianStatement : Prop :=
  ∀ (P : Polynomial ℂ) (e : Fin 2), ∃ Q : Polynomial ℂ, ∀ u, 0 < u.re →
    zeta (polynomialGaussian P) e u = Q.eval u * Gammaℝ (u + e.val)

theorem realTatePolynomialGaussian : RealTatePolynomialGaussianStatement := by
  classical
  intro P e
  choose Q hQ using fun m => zeta_monomialGaussian m e
  refine ⟨∑ m ∈ P.support, C (P.coeff m) * Q m, fun u hu => ?_⟩
  have hsum (x : ℝ) : integrand (polynomialGaussian P) e u x =
      ∑ m ∈ P.support, P.coeff m * integrand (monomialGaussian m) e u x := by
    unfold integrand
    split_ifs with hx
    · simp
    · simp only [polynomialGaussian, sum_apply, smul_apply, smul_eq_mul,
        Finset.sum_mul, mul_assoc]
  have hZ : zeta (polynomialGaussian P) e u =
      ∑ m ∈ P.support, P.coeff m * zeta (monomialGaussian m) e u := by
    simp only [zeta, hsum, integral_finsetSum _ (fun m _ =>
      (integrable_integrand (monomialGaussian m) e hu).const_mul _), integral_const_mul]
  simp only [hZ, hQ _ u hu, eval_finsetSum, eval_mul, eval_C, Finset.sum_mul, mul_assoc]

end Langlands.LocalFactor.RealTate
