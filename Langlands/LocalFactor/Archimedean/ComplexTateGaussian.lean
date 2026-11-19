import Langlands.LocalFactor.Archimedean.ComplexTateZeta
import Langlands.Global.Hecke.MixedSpaceFourier

/-! # Angular Gaussians for the complex Tate zeta integral -/

noncomputable section

open Complex Filter MeasureTheory
open scoped ComplexConjugate ContDiff ENNReal FourierTransform SchwartzMap

namespace Langlands.LocalFactor.ComplexTate

open Langlands.Global.Hecke

/-- The angular Gaussian in the normalization of the complex Tate statement. -/
def gaussian (m : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ m then starRingEnd ℂ z ^ m.natAbs else z ^ m.natAbs) *
    Complex.exp (-2 * (Real.pi : ℂ) * (‖z‖ : ℂ) ^ 2) / (Real.pi : ℂ)

private theorem gaussian_eq_complexGaussian (m : ℤ) (z : ℂ) :
    gaussian m z = complexGaussian 1 m z / (Real.pi : ℂ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simp [gaussian, complexGaussian, neg_mul]
  · by_cases hn : 0 ≤ -(n : ℤ)
    · have : n = 0 := by omega
      subst n
      simp [gaussian, complexGaussian, neg_mul]
    · have hn' : n ≠ 0 := by omega
      simp [gaussian, complexGaussian, hn', neg_mul]

private def gaussianExponent (z : ℂ) : ℝ :=
  -(2 * Real.pi * ‖z‖ ^ 2)

private theorem gaussianExponent_hasTemperateGrowth :
    gaussianExponent.HasTemperateGrowth := by
  unfold gaussianExponent
  fun_prop

private def radialSchwartz : 𝓢(ℂ, ℝ) where
  toFun := Real.exp ∘ gaussianExponent
  smooth' := Real.contDiff_exp.comp gaussianExponent_hasTemperateGrowth.1
  decay' k n := by
    obtain ⟨l, C, _, hderiv⟩ := gaussianExponent_hasTemperateGrowth.norm_iteratedFDeriv_le_uniform n
    obtain ⟨B, _, hgauss⟩ := exists_exp_neg_mul_sq_le_rpow (c := 2 * Real.pi)
      (by positivity) ((k + l * n : ℕ) : ℝ)
    let A := max 1 C
    refine ⟨(n.factorial : ℝ) * A ^ n * B, fun z => ?_⟩
    let R := 1 + ‖z‖
    have hR : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg z)
    have hA : 1 ≤ A := le_max_left _ _
    have hD : 1 ≤ A * R ^ l := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hR)
    have hbound := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := gaussianExponent) (n := n)
      Real.contDiff_exp gaussianExponent_hasTemperateGrowth.1 (by exact_mod_cast le_top) z
      (C := Real.exp (gaussianExponent z)) (D := A * R ^ l)
      (fun i _ => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
          Real.iter_deriv_exp, Real.norm_eq_abs, Real.abs_exp])
      (fun i hi hin => (hderiv i hin z).trans <|
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans
          (le_self_pow₀ hD (by omega)))
    have hdecay : R ^ (k + l * n) * Real.exp (gaussianExponent z) ≤ B := by
      have h := hgauss ‖z‖ (norm_nonneg z)
      change Real.exp (gaussianExponent z) ≤ B * R ^ (-((k + l * n : ℕ) : ℝ)) at h
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, le_mul_inv_iff₀ (by positivity)] at h
      rwa [mul_comm]
    calc
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ gaussianExponent) z‖
          ≤ R ^ k * ((n.factorial : ℝ) * Real.exp (gaussianExponent z) * (A * R ^ l) ^ n) := by
            gcongr
            exact le_add_of_nonneg_left zero_le_one
      _ = (n.factorial : ℝ) * A ^ n * (R ^ (k + l * n) * Real.exp (gaussianExponent z)) := by
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      _ ≤ (n.factorial : ℝ) * A ^ n * B := mul_le_mul_of_nonneg_left hdecay (by positivity)

private theorem gaussianWeight_hasTemperateGrowth (m : ℤ) :
    (fun z : ℂ => if 0 ≤ m then starRingEnd ℂ z ^ m.natAbs else z ^ m.natAbs).HasTemperateGrowth := by
  by_cases hm : 0 ≤ m
  · simp only [ite_eq_left hm]
    have h : (fun z : ℂ => starRingEnd ℂ z).HasTemperateGrowth := conjCLE.hasTemperateGrowth
    fun_prop
  · simp only [ite_eq_right hm]
    fun_prop

/-- The angular Gaussian regarded as a Schwartz function. -/
def gaussSchwartz (m : ℤ) : 𝓢(ℂ, ℂ) :=
  (Real.pi : ℂ)⁻¹ • SchwartzMap.smulLeftCLM ℂ
    (fun z => if 0 ≤ m then starRingEnd ℂ z ^ m.natAbs else z ^ m.natAbs)
    (radialSchwartz.postcompCLM ofRealCLM)

theorem gaussSchwartz_apply (m : ℤ) (z : ℂ) : gaussSchwartz m z = gaussian m z := by
  have hradial : (radialSchwartz z : ℂ) =
      Complex.exp (-2 * (Real.pi : ℂ) * (‖z‖ : ℂ) ^ 2) := by
    change (Real.exp (gaussianExponent z) : ℂ) = _
    rw [ofReal_exp]
    congr 1
    push_cast [gaussianExponent]
    ring
  simp only [gaussSchwartz, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (gaussianWeight_hasTemperateGrowth m),
    SchwartzMap.postcompCLM_apply, ofRealCLM_apply, smul_eq_mul, hradial, gaussian]
  ring

/-- The positive trace Fourier transform reverses the angular weight. -/
theorem integral_exp_mul_gaussian (m : ℤ) (y : ℂ) :
    ∫ z : ℂ, Complex.exp (4 * (Real.pi : ℂ) * I * ((z * y).re : ℂ)) *
        gaussian m z ∂measure =
      I ^ m.natAbs * gaussian (-m) y := by
  have hfun (z : ℂ) :
      Complex.exp (4 * (Real.pi : ℂ) * I * ((z * y).re : ℂ)) * gaussian m z =
        (complexGaussian 1 m z * (𝐞 (2 * (z * y).re) : ℂ)) / (Real.pi : ℂ) := by
    have hchar : (𝐞 (2 * (z * y).re) : ℂ) =
        Complex.exp (4 * (Real.pi : ℂ) * I * ((z * y).re : ℂ)) := by
      rw [Real.fourierChar_apply]
      congr 1
      push_cast
      ring
    rw [hchar, gaussian_eq_complexGaussian, ← mul_div_assoc, mul_comm (Complex.exp _)]
  have h := integral_complexGaussian_mul_fourierChar (a := 1) one_ne_zero m y
  simp only [norm_one, one_mul, mul_one] at h
  rw [measure, integral_smul_measure]
  simp_rw [hfun]
  rw [integral_div, h, gaussian_eq_complexGaussian, Algebra.smul_def]
  norm_num
  ring

/-- The angular Gaussian gives precisely the complex Gamma factor. -/
theorem zeta_gaussian (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    zeta (gaussian m) m u = Gammaℂ (u + (m.natAbs : ℂ) / 2) := by
  have hpos : 0 < (u + 0 + (m.natAbs : ℂ) / 2).re := by
    simp only [add_zero, add_re, div_ofNat_re, natCast_re]
    positivity
  have h := integral_complexGaussian_mul_complexCharFun (b := 1) one_pos m 0 u hpos
  simp only [add_zero, ofReal_one, one_cpow, mul_one] at h
  have hae : integrand (gaussian m) m u =ᵐ[volume] fun z : ℂ =>
      (complexGaussian 1 m z * complexCharFun m 0 z * (‖z‖ : ℂ) ^ (2 * (u - 1))) /
        (Real.pi : ℂ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
    simp only [integrand, hz, ite_false, direction, gaussian_eq_complexGaussian,
      complexCharFun, mul_zero, cpow_zero, mul_one]
    rw [show 2 * (u - 1) = 2 * u - 2 by ring]
    ring
  rw [zeta, measure, integral_smul_measure, integral_congr_ae hae, integral_div, h,
    Algebra.smul_def]
  norm_num [Complex.coe_algebraMap]
  field_simp [Real.pi_ne_zero]

end Langlands.LocalFactor.ComplexTate
