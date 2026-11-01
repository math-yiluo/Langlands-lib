import Langlands.Representation.RankinSelberg.BilateralSpectralCoefficientUniquenessStatement
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg

namespace BilateralSpectralCoefficientUniqueness

private theorem fourierCoeff_tsum (c : ℤ → ℂ) (hc : Summable (fun m => ‖c m‖))
    (n : ℤ) :
    fourierCoeff (T := 1)
      (fun x => ∑' m : ℤ, c m * fourier m x) n = c n := by
  have hpoint (x : AddCircle (1 : ℝ)) : Summable (fun m => c m * fourier m x) := by
    apply Summable.of_norm
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using hc
  let F : ℤ → AddCircle (1 : ℝ) → ℂ :=
    fun m x => fourier (-n) x * (c m * fourier m x)
  have hnorm (m : ℤ) (x : AddCircle (1 : ℝ)) : ‖F m x‖ = ‖c m‖ := by
    simp only [F, norm_mul, fourier_apply, Circle.norm_coe, one_mul, mul_one]
  have hint (m : ℤ) : Integrable (F m) AddCircle.haarAddCircle := by
    apply Integrable.of_bound
      (((fourier (-n)).continuous).mul
        (continuous_const.mul (fourier m).continuous)).aestronglyMeasurable
      ‖c m‖
    exact Filter.Eventually.of_forall fun x => (hnorm m x).le
  have hsum : Summable (fun m => ∫ x, ‖F m x‖ ∂AddCircle.haarAddCircle) := by
    simpa only [hnorm, integral_const, probReal_univ, one_smul] using hc
  have hcoeff (m : ℤ) :
      fourierCoeff (T := 1) (fun x => c m * fourier m x) n =
        c m * (Pi.single m (1 : ℂ) : ℤ → ℂ) n := by
    rw [fourierCoeff.const_mul]
    change c m * fourierCoeff (fourier m) n = _
    rw [fourierCoeff_fourier]
  calc
    _ = ∫ x, ∑' m : ℤ, F m x ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        ((hpoint x).hasSum.mul_left (fourier (-n) x)).tsum_eq.symm
    _ = ∑' m : ℤ, fourierCoeff (T := 1)
        (fun x => c m * fourier m x) n :=
      (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = c n := by
      rw [tsum_eq_single n]
      · simp only [hcoeff, Pi.single_eq_same, mul_one]
      · intro m hm
        rw [hcoeff, Pi.single_eq_of_ne (Ne.symm hm), mul_zero]

private theorem spectralPoint_vertical (q : ℕ) (hq : 1 < q) (σ t : ℝ) :
    spectralPoint q ((σ : ℂ) - ((2 * Real.pi * t / Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) =
      spectralPoint q (σ : ℂ) * fourier (T := 1) 1 (t : AddCircle (1 : ℝ)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hq).ne'
  have hlog : (Real.log (q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hq)).ne'
  have hclog : Complex.log (q : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log]
    exact hlog
  simp only [spectralPoint, Complex.cpow_def_of_ne_zero hq0, fourier_coe_apply,
    Int.cast_one, mul_one, Complex.ofReal_one, div_one]
  rw [← Complex.exp_add, ← Complex.natCast_log]
  congr 1
  push_cast
  field_simp [hclog]
  ring

private theorem fourier_one_zpow (x : AddCircle (1 : ℝ)) (m : ℤ) :
    fourier 1 x ^ m = fourier m x := by
  rw [fourier_one, fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]

end BilateralSpectralCoefficientUniqueness

/-- Absolutely convergent bilateral spectral sums that agree throughout a right
half-plane have equal original coefficient functions. -/
theorem bilateralSpectralCoefficientUniqueness :
    BilateralSpectralCoefficientUniquenessStatement := by
  intro q hq a b
  rintro ⟨C, h⟩
  let σ : ℝ := C + 1
  have hσ : C < σ := by dsimp [σ]; linarith
  let r : ℂ := spectralPoint q (σ : ℂ)
  have hr : r ≠ 0 := spectralPoint_ne_zero_of_pos (lt_trans Nat.zero_lt_one hq) _
  have hreal := h (σ : ℂ) hσ
  have heq (x : AddCircle (1 : ℝ)) :
      (∑' m : ℤ, (a m * r ^ m) * fourier m x) =
        ∑' m : ℤ, (b m * r ^ m) * fourier m x := by
    induction x using QuotientAddGroup.induction_on
    rename_i t
    have hs : C < ((σ : ℂ) -
        ((2 * Real.pi * t / Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I).re := by
      simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero] using hσ
    have he := (h _ hs).2.2
    rw [BilateralSpectralCoefficientUniqueness.spectralPoint_vertical q hq σ t] at he
    simpa only [mul_zpow, BilateralSpectralCoefficientUniqueness.fourier_one_zpow,
      ← mul_assoc] using he
  apply Langlands.HarmonicAnalysis.BilateralLaurentSeries.ext
  intro n
  have hcoeff := congrArg (fun f : AddCircle (1 : ℝ) → ℂ => fourierCoeff f n)
    (funext heq)
  rw [BilateralSpectralCoefficientUniqueness.fourierCoeff_tsum _ hreal.1,
    BilateralSpectralCoefficientUniqueness.fourierCoeff_tsum _ hreal.2.1] at hcoeff
  exact mul_right_cancel₀ (zpow_ne_zero n hr) hcoeff

end Langlands.RankinSelberg
