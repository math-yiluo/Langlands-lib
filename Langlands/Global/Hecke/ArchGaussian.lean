import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Archimedean Gaussians: Fourier transforms and local zeta integrals

The adapted Gaussian test functions of Tate's thesis (§2.5) at the real and complex places,
their Fourier transforms against the additive characters `x ↦ 𝐞 (a x y)` on `ℝ` and
`z ↦ 𝐞 (2 Re (a z w))` on `ℂ`, and their local zeta integrals against the characters
`sgn ^ p |·| ^ t` and `(z / |z|) ^ N |z| ^ (2 t)`. All integrals are for Lebesgue measure.

* `realGaussian b p x = x ^ p exp (-π b x²)`; `integral_realGaussian_zero_mul_fourierChar`,
  `integral_realGaussian_one_mul_fourierChar` and `integral_realGaussian_mul_realCharFun`.
* `complexGaussian b N z = z̄ ^ N exp (-2π b |z|²)` (`N ≥ 0`), `z ^ (-N) exp (-2π b |z|²)`
  (`N < 0`); `integral_complexGaussian_mul_fourierChar` and
  `integral_complexGaussian_mul_complexCharFun`.

The complex Fourier transform is computed from the moments
`cMoment b u n = ∫ z̄ ^ n exp (-2π b |z|²) 𝐞 (2 Re (u z)) dz`, which satisfy
`cMoment b u (n + 1) = (i u / b) cMoment b u n` by integration by parts along the real
directions `1` and `i`.
-/

open MeasureTheory Set Filter Complex
open scoped Real ComplexConjugate FourierTransform RealInnerProductSpace

noncomputable section

namespace Langlands.Global.Hecke

/-! ### Polynomially weighted Gaussians -/

section Integrability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- `x ↦ ‖x‖ ^ k * exp (-c ‖x‖²)` is integrable for every additive Haar measure. -/
theorem integrable_norm_pow_mul_exp_neg_mul_sq (μ : Measure E) [μ.IsAddHaarMeasure]
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ k * Real.exp (-c * ‖x‖ ^ 2)) μ := by
  refine (integrable_fun_norm_addHaar μ (f := fun y : ℝ => y ^ k * Real.exp (-c * y ^ 2))).2 ?_
  have := integrableOn_rpow_mul_exp_neg_mul_sq hc
    (s := ((Module.finrank ℝ E - 1 + k : ℕ) : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E - 1 + k); linarith)
  refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul, Real.rpow_natCast, pow_add]
  ring

/-- A function dominated by a polynomially weighted Gaussian is integrable. -/
theorem integrable_of_norm_le_pow_mul_exp (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] {f : E → F} (hf : AEStronglyMeasurable f μ)
    {c : ℝ} (hc : 0 < c) (k : ℕ) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * (‖x‖ ^ k * Real.exp (-c * ‖x‖ ^ 2))) : Integrable f μ :=
  ((integrable_norm_pow_mul_exp_neg_mul_sq μ hc k).const_mul C).mono' hf (ae_of_all _ h)

end Integrability

/-! ### Complex powers of positive reals and the Gaussian Mellin transform -/

theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = cexp (Real.log x * z) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hx.ne'), ofReal_log hx.le]

theorem ofReal_rpow_cpow {x : ℝ} (hx : 0 < x) (r : ℝ) (z : ℂ) :
    ((x ^ r : ℝ) : ℂ) ^ z = (x : ℂ) ^ ((r : ℂ) * z) := by
  rw [ofReal_cpow_eq_exp (Real.rpow_pos_of_pos hx r), ofReal_cpow_eq_exp hx,
    Real.log_rpow hx]
  push_cast
  ring_nf

/-- `∫_0^∞ y ^ (w - 1) exp (-c y²) dy = ½ (1/c) ^ (w/2) Γ(w/2)`. -/
theorem integral_Ioi_cpow_mul_exp_neg_mul_sq {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 1) * cexp (-(c * (y : ℂ) ^ 2)) =
      (1 / 2 : ℂ) * ((1 / (c : ℂ)) ^ (w / 2) * Gamma (w / 2)) := by
  have key := integral_cpow_mul_exp_neg_mul_Ioi (a := w / 2) (r := c)
    (by simpa using div_pos hw two_pos) hc
  rw [← integral_comp_rpow_Ioi_of_pos (p := 2) two_pos] at key
  rw [← key, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy'.ne'
  simp only [real_smul]
  rw [ofReal_rpow_cpow hy' 2 (w / 2 - 1)]
  rw [show w - 1 = (w - 2) + 1 by ring, cpow_add _ _ hy0, cpow_one]
  norm_num
  rw [show (2 : ℂ) * (w / 2 - 1) = w - 2 by ring]
  ring

/-! ### Radial Gaussian Mellin transforms -/

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Mellin transform of a radial Gaussian on a finite-dimensional real normed space:
`∫ ‖x‖ ^ (w - n) exp (-c ‖x‖²) dμ = (n μ(B(0,1)) / 2) (1/c) ^ (w/2) Γ(w/2)`, `n = dim E`. -/
theorem integral_norm_cpow_mul_exp_neg_mul_sq (μ : Measure E) [μ.IsAddHaarMeasure]
    {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    ∫ x, ((‖x‖ : ℝ) : ℂ) ^ (w - Module.finrank ℝ E) * cexp (-((c : ℂ) * ((‖x‖ : ℝ) : ℂ) ^ 2)) ∂μ =
      ((Module.finrank ℝ E * μ.real (Metric.ball 0 1) / 2 : ℝ) : ℂ) *
        ((1 / (c : ℂ)) ^ (w / 2) * Gamma (w / 2)) := by
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  rw [integral_fun_norm_addHaar μ (fun y : ℝ => (y : ℂ) ^ (w - Module.finrank ℝ E) *
    cexp (-((c : ℂ) * (y : ℂ) ^ 2)))]
  have h : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) •
      ((y : ℂ) ^ (w - Module.finrank ℝ E) * cexp (-((c : ℂ) * (y : ℂ) ^ 2))) =
      ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 1) * cexp (-((c : ℂ) * (y : ℂ) ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hy)
    rw [real_smul, ← mul_assoc, ofReal_pow, ← cpow_natCast, ← cpow_add _ _ hy0,
      Nat.cast_sub hn]
    congr 2
    push_cast
    ring
  rw [h, integral_Ioi_cpow_mul_exp_neg_mul_sq hw hc, nsmul_eq_mul, real_smul]
  push_cast
  ring

end Radial

/-! ### The real place -/

/-- The adapted real Gaussian `x ↦ x ^ p * exp (-π b x²)`. -/
def realGaussian (b : ℝ) (p : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ p * cexp (-(π * b * (x : ℂ) ^ 2))

/-- The real character `x ↦ (x / |x|) ^ p * |x| ^ t`, as a function on the real line. -/
def realCharFun (p : ℕ) (t : ℂ) (x : ℝ) : ℂ :=
  ((x / |x| : ℝ) : ℂ) ^ p * ((|x| : ℝ) : ℂ) ^ t

theorem integral_realGaussian_zero_mul_fourierChar {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    ∫ x : ℝ, realGaussian |a| 0 x * 𝐞 (a * x * y) =
      ((Real.sqrt |a|)⁻¹ : ℝ) * realGaussian |a| 0 y := by
  have hb : 0 < |a| := abs_pos.2 ha
  have hB : (-((π : ℂ) * |a|)).re < 0 := by
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, neg_lt_zero]
    positivity
  have h := integral_cexp_quadratic hB (2 * π * a * y * I) 0
  have hfun : (fun x : ℝ => realGaussian |a| 0 x * 𝐞 (a * x * y)) =
      fun x : ℝ => cexp (-((π : ℂ) * |a|) * (x : ℂ) ^ 2 + (2 * π * a * y * I) * x + 0) := by
    funext x
    simp only [realGaussian, pow_zero, one_mul, Real.fourierChar_apply]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun, h]
  simp only [realGaussian, pow_zero, one_mul]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have ha' : ((|a| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  congr 1
  · rw [neg_neg, show (π : ℂ) / (π * |a|) = ((|a|⁻¹ : ℝ) : ℂ) by push_cast; field_simp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (inv_nonneg.2 hb.le), Real.sqrt_eq_rpow, Real.inv_rpow hb.le]
  · congr 1
    have hsq : (a : ℂ) ^ 2 = ((|a| : ℝ) : ℂ) ^ 2 := by exact_mod_cast (sq_abs a).symm
    field_simp
    linear_combination (-4 * π * y ^ 2 : ℂ) * hsq + (4 * π * y ^ 2 * a ^ 2 : ℂ) * I_sq

theorem realGaussian_mul_fourierChar (a : ℝ) (p : ℕ) (x y : ℝ) :
    realGaussian |a| p x * 𝐞 (a * x * y) =
      (x : ℂ) ^ p * cexp (-((π : ℂ) * |a|) * (x : ℂ) ^ 2 + (2 * π * a * y * I) * x + 0) := by
  simp only [realGaussian, Real.fourierChar_apply, mul_assoc]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The Fourier transform of the odd adapted Gaussian `x exp (-π |a| x²)`. -/
theorem integral_realGaussian_one_mul_fourierChar {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    ∫ x : ℝ, realGaussian |a| 1 x * 𝐞 (a * x * y) =
      ((Real.sqrt |a|)⁻¹ : ℝ) * (I * ((a / |a| : ℝ) : ℂ)) * realGaussian |a| 1 y := by
  have hb : 0 < |a| := abs_pos.2 ha
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have ha' : ((|a| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  set B : ℂ := -((π : ℂ) * |a|) with hBdef
  set C : ℂ := 2 * π * a * y * I with hCdef
  have hB : B.re < 0 := by
    simp only [hBdef, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, neg_lt_zero]
    positivity
  have hB0 : B ≠ 0 := by
    rw [hBdef, neg_ne_zero]
    exact mul_ne_zero hπ ha'
  set q : ℝ → ℂ := fun x => cexp (B * (x : ℂ) ^ 2 + C * x + 0) with hqdef
  have hq_int : Integrable q := integrable_cexp_quadratic' hB C 0
  have hq_cont : Continuous q := by rw [hqdef]; fun_prop
  have hnorm : ∀ x : ℝ, ‖q x‖ = Real.exp (-(π * |a|) * ‖x‖ ^ 2) := by
    intro x
    have hq_eq : q x = cexp (((-(π * |a| * x ^ 2)) : ℝ) + ((2 * π * a * y * x : ℝ) : ℂ) * I) := by
      simp only [hqdef, hBdef, hCdef]
      congr 1
      push_cast
      ring
    rw [hq_eq, Complex.norm_exp]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
      add_zero, Real.norm_eq_abs, sq_abs]
    ring_nf
  have hxq_int : Integrable (fun x : ℝ => (x : ℂ) * q x) := by
    refine integrable_of_norm_le_pow_mul_exp volume
      ((continuous_ofReal.mul hq_cont).aestronglyMeasurable) (mul_pos Real.pi_pos hb) 1 1
      (fun x => le_of_eq ?_)
    rw [norm_mul, hnorm x, Complex.norm_real]
    ring_nf
  have hderiv : ∀ x : ℝ, HasDerivAt q (q x * (B * (2 * x) + C)) x := by
    intro x
    have h1 : HasDerivAt (fun w : ℂ => B * w ^ 2 + C * w + 0) (B * (2 * x) + C) (x : ℂ) := by
      have := (((hasDerivAt_pow 2 (x : ℂ)).const_mul B).add
        ((hasDerivAt_id (x : ℂ)).const_mul C)).add_const 0
      convert this using 1 <;> simp
    exact h1.cexp.comp_ofReal
  have hderiv_int : Integrable (fun x : ℝ => q x * (B * (2 * x) + C)) := by
    have : (fun x : ℝ => q x * (B * (2 * x) + C)) =
        fun x : ℝ => (2 * B) * ((x : ℂ) * q x) + C * q x := by
      funext x; ring
    rw [this]
    exact (hxq_int.const_mul _).add (hq_int.const_mul _)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hderiv_int hq_int
  have hsplit : ∫ x : ℝ, q x * (B * (2 * x) + C) =
      (2 * B) * (∫ x : ℝ, (x : ℂ) * q x) + C * ∫ x, q x := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hxq_int.const_mul _) (hq_int.const_mul _)]
    congr 1
    funext x
    ring
  have hQ : ∫ x, q x = ((Real.sqrt |a|)⁻¹ : ℝ) * cexp (-(π * |a| * (y : ℂ) ^ 2)) := by
    have := integral_realGaussian_zero_mul_fourierChar ha y
    rw [show (fun x : ℝ => realGaussian |a| 0 x * 𝐞 (a * x * y)) = q from
      funext fun x => by rw [realGaussian_mul_fourierChar, pow_zero, one_mul]] at this
    rw [this]
    simp [realGaussian]
  have hfun : (fun x : ℝ => realGaussian |a| 1 x * 𝐞 (a * x * y)) =
      fun x : ℝ => (x : ℂ) * q x := by
    funext x
    rw [realGaussian_mul_fourierChar, pow_one]
  have hX : ∫ x : ℝ, (x : ℂ) * q x = -(C / (2 * B)) * ∫ x, q x := by
    rw [hsplit] at h0
    field_simp
    linear_combination h0
  have hCB : -(C / (2 * B)) = I * ((a / |a| : ℝ) : ℂ) * y := by
    rw [hBdef, hCdef]
    push_cast
    field_simp
  rw [hfun, hX, hQ, hCB]
  simp only [realGaussian, pow_one]
  ring

/-- The real local zeta integral of the adapted Gaussian against `sgn ^ p |·| ^ t`:
`∫ x ^ p e ^ (-π b x²) sgn(x) ^ p |x| ^ t |x| ^ (s - 1) dx = b ^ (-(s + t + p)/2) Γ_ℝ(s + t + p)`. -/
theorem integral_realGaussian_mul_realCharFun {b : ℝ} (hb : 0 < b) (p : ℕ)
    (t s : ℂ) (hs : 0 < (s + t + p).re) :
    ∫ x : ℝ, realGaussian b p x * realCharFun p t x * ((|x| : ℝ) : ℂ) ^ (s - 1) =
      (b : ℂ) ^ (-(s + t + p) / 2) * Gammaℝ (s + t + p) := by
  have key := integral_norm_cpow_mul_exp_neg_mul_sq (E := ℝ) volume hs (mul_pos Real.pi_pos hb)
  simp only [Module.finrank_self, Real.norm_eq_abs, Nat.cast_one] at key
  have hball : volume.real (Metric.ball (0 : ℝ) 1) = 2 := by
    simp [Measure.real, Real.volume_ball]
  rw [hball] at key
  have hae : (fun x : ℝ => realGaussian b p x * realCharFun p t x * ((|x| : ℝ) : ℂ) ^ (s - 1))
      =ᵐ[volume] fun x => ((|x| : ℝ) : ℂ) ^ (s + t + p - 1) *
        cexp (-(((π * b : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ 2)) := by
    filter_upwards [Measure.ae_ne volume 0] with x hx
    have hx' : (0 : ℝ) < |x| := abs_pos.2 hx
    have hx0 : ((|x| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx'.ne'
    have h1 : (x : ℂ) ^ p * ((x / |x| : ℝ) : ℂ) ^ p = ((|x| : ℝ) : ℂ) ^ (p : ℂ) := by
      rw [cpow_natCast, ← mul_pow, ← ofReal_mul]
      congr 2
      field_simp
      exact (sq_abs x).symm
    have h2 : (x : ℂ) ^ 2 = ((|x| : ℝ) : ℂ) ^ 2 := by exact_mod_cast (sq_abs x).symm
    simp only [realGaussian, realCharFun]
    rw [h2, show s + t + p - 1 = (p : ℂ) + t + (s - 1) by ring, cpow_add _ _ hx0,
      cpow_add _ _ hx0, ← h1]
    push_cast
    ring
  rw [integral_congr_ae hae, key, Gammaℝ_def]
  have hpb : ((π * b : ℝ) : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg (mul_pos Real.pi_pos hb).le]
    exact Real.pi_ne_zero.symm
  rw [one_div, inv_cpow _ _ hpb, ← cpow_neg, ofReal_mul,
    mul_cpow_ofReal_nonneg Real.pi_pos.le hb.le, neg_div,
    show ((1 * 2 / 2 : ℝ) : ℂ) = 1 by norm_num, one_mul]
  ring

/-! ### The complex place -/

section ComplexPlace

/-- The Gaussian `exp (-2π b z z̄)`, written through `z` and `z̄`. -/
def cGauss (b : ℝ) (z : ℂ) : ℂ := cexp (-(2 * π * b : ℂ) * (z * conj z))

/-- The character `z ↦ exp (2π i (u z + ū z̄)) = 𝐞 (2 Re (u z))`. -/
def cChar (u : ℂ) (z : ℂ) : ℂ := cexp (2 * π * I * (u * z + conj u * conj z))

theorem cGauss_eq (b : ℝ) (z : ℂ) :
    cGauss b z = cexp (-(2 * π * b * ((‖z‖ : ℝ) : ℂ) ^ 2)) := by
  rw [cGauss, mul_conj']
  ring_nf

theorem norm_cGauss (b : ℝ) (z : ℂ) : ‖cGauss b z‖ = Real.exp (-(2 * π * b) * ‖z‖ ^ 2) := by
  rw [cGauss_eq, Complex.norm_exp]
  congr 1
  rw [show -(2 * (π : ℂ) * b * ((‖z‖ : ℝ) : ℂ) ^ 2) = ((-(2 * π * b) * ‖z‖ ^ 2 : ℝ) : ℂ) by
    push_cast; ring, ofReal_re]

theorem continuous_cGauss (b : ℝ) : Continuous (cGauss b) := by
  unfold cGauss
  exact Complex.continuous_exp.comp (continuous_const.mul (continuous_id.mul continuous_conj))

theorem cChar_eq (u z : ℂ) : cChar u z = 𝐞 (2 * (u * z).re) := by
  rw [cChar, Real.fourierChar_apply]
  congr 1
  rw [← map_mul, add_conj]
  push_cast
  ring

theorem norm_cChar (u z : ℂ) : ‖cChar u z‖ = 1 := by
  rw [cChar_eq]
  exact Circle.norm_coe _

theorem continuous_cChar (u : ℂ) : Continuous (cChar u) := by
  unfold cChar
  exact Complex.continuous_exp.comp (continuous_const.mul
    ((continuous_const.mul continuous_id).add (continuous_const.mul continuous_conj)))

theorem conj_cGauss (b : ℝ) (z : ℂ) : conj (cGauss b z) = cGauss b z := by
  rw [cGauss_eq, ← exp_conj]
  congr 1
  simp only [map_neg, map_mul, map_pow, conj_ofReal, map_ofNat]

theorem conj_cChar (u z : ℂ) : conj (cChar u z) = cChar (-u) z := by
  rw [cChar, cChar, ← exp_conj]
  congr 1
  simp only [map_mul, map_add, map_ofNat, conj_ofReal, conj_I, conj_conj, map_neg]
  ring

theorem integrable_monomial_mul_cGauss {b : ℝ} (hb : 0 < b) (k l : ℕ) {h : ℂ → ℂ}
    (hh : Continuous h) (hh1 : ∀ z, ‖h z‖ = 1) :
    Integrable (fun z : ℂ => z ^ k * conj z ^ l * cGauss b z * h z) := by
  refine integrable_of_norm_le_pow_mul_exp volume ?_ (by positivity : 0 < 2 * π * b) (k + l) 1
    (fun z => le_of_eq ?_)
  · exact ((((continuous_id.pow k).mul (continuous_conj.pow l)).mul
      (continuous_cGauss b)).mul hh).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_mul, hh1, norm_cGauss, norm_pow, norm_pow, Complex.norm_conj,
      pow_add]
    ring

/-- A line derivative computed through a complex-differentiable expression of the parameter. -/
theorem hasLineDerivAt_of_comp_ofReal {f Φ : ℂ → ℂ} {f' : ℂ} (z v : ℂ)
    (hΦ : ∀ t : ℝ, f (z + t • v) = Φ t) (hd : HasDerivAt Φ f' 0) :
    HasLineDerivAt ℝ f f' z v := by
  unfold HasLineDerivAt
  rw [show (fun t : ℝ => f (z + t • v)) = fun t : ℝ => Φ t from funext hΦ]
  have hd' : HasDerivAt Φ f' ((0 : ℝ) : ℂ) := by rwa [ofReal_zero]
  exact hd'.comp_ofReal

/-- The moments `∫ z̄ ^ n exp (-2π b |z|²) 𝐞 (2 Re (u z)) dz`. -/
def cMoment (b : ℝ) (u : ℂ) (n : ℕ) : ℂ := ∫ z : ℂ, conj z ^ n * cGauss b z * cChar u z

theorem cMoment_zero {b : ℝ} (hb : 0 < b) (u : ℂ) :
    cMoment b u 0 = ((2 * b)⁻¹ : ℝ) * cexp (-(2 * π * ‖u‖ ^ 2 / b : ℝ)) := by
  have hb' : 0 < (2 * π * b : ℂ).re := by
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
    positivity
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb' (4 * π * I) (conj u)
  rw [Complex.finrank_real_complex] at h
  have hfun : (fun z : ℂ => conj z ^ 0 * cGauss b z * cChar u z) = fun z : ℂ =>
      cexp (-(2 * π * b : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2 + (4 * π * I) * ((inner ℝ (conj u) z : ℝ) : ℂ)) := by
    funext z
    rw [pow_zero, one_mul, cGauss, cChar, ← Complex.exp_add, Complex.inner, conj_conj, mul_conj',
      ← map_mul, add_conj, mul_comm z u]
    push_cast
    ring_nf
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  rw [cMoment, hfun, h, Complex.norm_conj]
  norm_num
  congr 1
  · field_simp
  · congr 1
    field_simp
    linear_combination (4 * ‖u‖ ^ 2 : ℂ) * I_sq

/-- Integration by parts along a real direction, for products of complex-valued functions. -/
theorem integral_mul_lineDeriv_eq_neg {f f' g g' : ℂ → ℂ} {v : ℂ}
    (hf'g : Integrable (fun z => f' z * g z)) (hfg' : Integrable (fun z => f z * g' z))
    (hfg : Integrable (fun z => f z * g z))
    (hf : ∀ z, HasLineDerivAt ℝ f (f' z) z v) (hg : ∀ z, HasLineDerivAt ℝ g (g' z) z v) :
    ∫ z, f z * g' z = -∫ z, f' z * g z :=
  integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) hf'g hfg' hfg (fun z _ => hf z) (fun z _ => hg z)

theorem hasLineDerivAt_conj_pow_mul_cGauss (b : ℝ) (n : ℕ) (z v : ℂ) :
    HasLineDerivAt ℝ (fun z => conj z ^ n * cGauss b z)
      (n * conj z ^ (n - 1) * conj v * cGauss b z +
        conj z ^ n * cGauss b z * (-(2 * π * b : ℂ) * (v * conj z + z * conj v))) z v := by
  refine hasLineDerivAt_of_comp_ofReal z v
    (Φ := fun s : ℂ => (conj z + s * conj v) ^ n *
      cexp (-(2 * π * b : ℂ) * ((z + s * v) * (conj z + s * conj v)))) (fun t => ?_) ?_
  · simp only [cGauss, real_smul, map_add, map_mul, conj_ofReal]
  · have h1 : HasDerivAt (fun s : ℂ => conj z + s * conj v) (conj v) 0 := by
      simpa using (hasDerivAt_id' (0 : ℂ)).mul_const (conj v) |>.const_add (conj z)
    have h3 : HasDerivAt (fun s : ℂ => z + s * v) v 0 := by
      simpa using (hasDerivAt_id' (0 : ℂ)).mul_const v |>.const_add z
    have h2 : HasDerivAt (fun s : ℂ => (z + s * v) * (conj z + s * conj v))
        (v * conj z + z * conj v) 0 := by
      convert h3.mul h1 using 1
      simp
    convert (h1.pow n).mul ((h2.const_mul (-(2 * π * b : ℂ))).cexp) using 1
    simp only [cGauss, Pi.pow_apply, zero_mul, add_zero]
    ring

theorem hasLineDerivAt_cChar (u z v : ℂ) :
    HasLineDerivAt ℝ (cChar u) (cChar u z * (2 * π * I * (u * v + conj u * conj v))) z v := by
  refine hasLineDerivAt_of_comp_ofReal z v
    (Φ := fun s : ℂ => cexp (2 * π * I * (u * (z + s * v) + conj u * (conj z + s * conj v))))
    (fun t => ?_) ?_
  · simp only [cChar, real_smul, map_add, map_mul, conj_ofReal]
  · have h1 : HasDerivAt (fun s : ℂ => conj z + s * conj v) (conj v) 0 := by
      simpa using (hasDerivAt_id' (0 : ℂ)).mul_const (conj v) |>.const_add (conj z)
    have h3 : HasDerivAt (fun s : ℂ => z + s * v) v 0 := by
      simpa using (hasDerivAt_id' (0 : ℂ)).mul_const v |>.const_add z
    have h := ((h3.const_mul u).add (h1.const_mul (conj u))).const_mul (2 * π * I)
    convert h.cexp using 1
    simp only [cChar, Pi.add_apply, zero_mul, add_zero]

theorem integral_sub_const_mul_eq_zero {F G : ℂ → ℂ} (hF : Integrable F) (hG : Integrable G)
    (h1 : ∫ z, F z = 0) (h2 : ∫ z, G z = 0) (c : ℂ) : ∫ z, (F z - c * G z) = 0 := by
  rw [integral_sub hF (hG.const_mul c), integral_const_mul, h1, h2, mul_zero, sub_zero]

theorem cMoment_succ {b : ℝ} (hb : 0 < b) (u : ℂ) (n : ℕ) :
    cMoment b u (n + 1) = (I * u / b) * cMoment b u n := by
  have hm : ∀ k l : ℕ, Integrable (fun z : ℂ => z ^ k * conj z ^ l * cGauss b z * cChar u z) :=
    fun k l => integrable_monomial_mul_cGauss hb k l (continuous_cChar u) (norm_cChar u)
  have hm' : ∀ l : ℕ, Integrable (fun z : ℂ => conj z ^ l * cGauss b z * cChar u z) :=
    fun l => by simpa using hm 0 l
  have hA : ∀ v : ℂ, Integrable (fun z : ℂ => (n * conj z ^ (n - 1) * conj v * cGauss b z +
      conj z ^ n * cGauss b z * (-(2 * π * b : ℂ) * (v * conj z + z * conj v))) * cChar u z) := by
    intro v
    refine ((((hm' (n - 1)).const_mul (n * conj v)).add
      ((hm' (n + 1)).const_mul (-(2 * π * b : ℂ) * v))).add
      ((hm 1 n).const_mul (-(2 * π * b : ℂ) * conj v))).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, pow_succ]
    ring
  have hB : ∀ v : ℂ, Integrable (fun z : ℂ =>
      conj z ^ n * cGauss b z * (cChar u z * (2 * π * I * (u * v + conj u * conj v)))) := by
    intro v
    refine ((hm' n).mul_const (2 * π * I * (u * v + conj u * conj v))).congr
      (Eventually.of_forall fun z => ?_)
    simp only
    ring
  have key : ∀ v : ℂ, ∫ z : ℂ, (conj z ^ n * cGauss b z *
      (cChar u z * (2 * π * I * (u * v + conj u * conj v))) +
      (n * conj z ^ (n - 1) * conj v * cGauss b z +
        conj z ^ n * cGauss b z * (-(2 * π * b : ℂ) * (v * conj z + z * conj v))) *
          cChar u z) = 0 := by
    intro v
    rw [integral_add (hB v) (hA v), integral_mul_lineDeriv_eq_neg (hA v) (hB v) (hm' n)
      (fun z => hasLineDerivAt_conj_pow_mul_cGauss b n z v)
      (fun z => hasLineDerivAt_cChar u z v), neg_add_cancel]
  have hcomb : ∫ z : ℂ, ((4 * π * I * u) * (conj z ^ n * cGauss b z * cChar u z) -
      (4 * π * b) * (conj z ^ (n + 1) * cGauss b z * cChar u z)) = 0 := by
    have e := integral_sub_const_mul_eq_zero ((hB 1).add (hA 1)) ((hB I).add (hA I))
      (key 1) (key I) I
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun z => ?_)) e
    simp only [Pi.add_apply, map_one, conj_I]
    linear_combination ((2 * π * I * (u - conj u)) * (conj z ^ n * cGauss b z * cChar u z) -
      n * (conj z ^ (n - 1) * cGauss b z * cChar u z) -
      (2 * π * b * (conj z - z)) * (conj z ^ n * cGauss b z * cChar u z)) * I_sq
  rw [integral_sub ((hm' n).const_mul _) ((hm' (n + 1)).const_mul _), integral_const_mul,
    integral_const_mul] at hcomb
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  have h4 : (4 * π : ℂ) * (b * cMoment b u (n + 1) - I * u * cMoment b u n) = 0 := by
    simp only [cMoment]
    linear_combination -hcomb
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h (mul_ne_zero (by norm_num) hπ)
  rw [div_mul_eq_mul_div, eq_div_iff hb0]
  linear_combination h

theorem cMoment_eq {b : ℝ} (hb : 0 < b) (u : ℂ) (n : ℕ) :
    cMoment b u n =
      (I * u / b) ^ n * (((2 * b)⁻¹ : ℝ) * cexp (-(2 * π * ‖u‖ ^ 2 / b : ℝ))) := by
  induction n with
  | zero => rw [cMoment_zero hb, pow_zero, one_mul]
  | succ n ih => rw [cMoment_succ hb, ih, pow_succ]; ring

theorem integral_pow_mul_cGauss_mul_cChar {b : ℝ} (hb : 0 < b) (u : ℂ) (n : ℕ) :
    ∫ z : ℂ, z ^ n * cGauss b z * cChar u z =
      (I * conj u / b) ^ n * (((2 * b)⁻¹ : ℝ) * cexp (-(2 * π * ‖u‖ ^ 2 / b : ℝ))) := by
  have h : (fun z : ℂ => z ^ n * cGauss b z * cChar u z) =
      fun z => conj (conj z ^ n * cGauss b z * cChar (-u) z) := by
    funext z
    rw [map_mul, map_mul, map_pow, conj_conj, conj_cGauss, conj_cChar, neg_neg]
  rw [h, integral_conj, ← cMoment, cMoment_eq hb]
  simp only [map_mul, map_pow, map_div₀, map_neg, conj_I, conj_ofReal, ← exp_conj, norm_neg]
  ring

/-- The adapted complex Gaussian: `z̄ ^ N exp (-2π b |z|²)` for `N ≥ 0`, and
`z ^ (-N) exp (-2π b |z|²)` for `N < 0`. -/
def complexGaussian (b : ℝ) (N : ℤ) (z : ℂ) : ℂ :=
  conj z ^ N.toNat * z ^ (-N).toNat * cexp (-(2 * π * b * ((‖z‖ : ℝ) : ℂ) ^ 2))

/-- The complex character `z ↦ (z / |z|) ^ N |z| ^ (2 t)`, as a function on `ℂ`. -/
def complexCharFun (N : ℤ) (t : ℂ) (z : ℂ) : ℂ :=
  (z / ((‖z‖ : ℝ) : ℂ)) ^ N * ((‖z‖ : ℝ) : ℂ) ^ (2 * t)

theorem complexGaussian_eq (b : ℝ) (N : ℤ) (z : ℂ) :
    complexGaussian b N z = conj z ^ N.toNat * z ^ (-N).toNat * cGauss b z := by
  rw [complexGaussian, cGauss_eq]

/-- The Fourier transform of the adapted complex Gaussian against `𝐞 (2 Re (a z w))`, for
Lebesgue measure on `ℂ`. -/
theorem integral_complexGaussian_mul_fourierChar {a : ℂ} (ha : a ≠ 0) (N : ℤ) (w : ℂ) :
    ∫ z : ℂ, complexGaussian ‖a‖ N z * 𝐞 (2 * (a * z * w).re) =
      ((2 * ‖a‖)⁻¹ : ℝ) * (I ^ N.natAbs * (a / ‖a‖) ^ N) * complexGaussian ‖a‖ (-N) w := by
  have hb : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hb0 : ((‖a‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  have hchar : ∀ z : ℂ, (𝐞 (2 * (a * z * w).re) : ℂ) = cChar (a * w) z := by
    intro z
    rw [cChar_eq]
    ring_nf
  have hexp : cexp (-(2 * π * ‖a * w‖ ^ 2 / ‖a‖ : ℝ)) = cGauss ‖a‖ w := by
    rw [cGauss_eq, norm_mul]
    congr 1
    push_cast
    field_simp
  simp_rw [hchar, complexGaussian_eq]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
  · simp only [Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, mul_one, one_mul,
      zpow_natCast, Int.natAbs_natCast, neg_neg]
    rw [← cMoment, cMoment_eq hb, hexp]
    ring
  · have hinv : (a / ‖a‖)⁻¹ = conj a / ‖a‖ := by
      rw [inv_div, div_eq_div_iff ha hb0, conj_mul']
      ring
    simp only [Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, mul_one, one_mul,
      Int.natAbs_neg, Int.natAbs_natCast, neg_neg, zpow_neg, zpow_natCast]
    rw [integral_pow_mul_cGauss_mul_cChar hb, hexp, ← inv_pow, hinv, map_mul]
    ring

theorem complexGaussian_mul_complexCharFun {z : ℂ} (hz : z ≠ 0) (b : ℝ) (N : ℤ) (t : ℂ) :
    complexGaussian b N z * complexCharFun N t z =
      ((‖z‖ : ℝ) : ℂ) ^ ((N.natAbs : ℂ) + 2 * t) *
        cexp (-(2 * π * b * ((‖z‖ : ℝ) : ℂ) ^ 2)) := by
  have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have key : conj z ^ N.toNat * z ^ (-N).toNat * (z / ((‖z‖ : ℝ) : ℂ)) ^ N =
      ((‖z‖ : ℝ) : ℂ) ^ N.natAbs := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
    · simp only [Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, mul_one, zpow_natCast,
        Int.natAbs_natCast]
      rw [← mul_pow]
      congr 1
      rw [mul_div_assoc', conj_mul', div_eq_iff hr]
      ring
    · simp only [Int.toNat_natCast, Int.toNat_neg_natCast, neg_neg, pow_zero, one_mul,
        Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
      rw [← inv_pow, inv_div, ← mul_pow]
      congr 1
      field_simp
  rw [complexGaussian, complexCharFun, cpow_add _ _ hr, cpow_natCast, ← key]
  ring

/-- The complex local zeta integral of the adapted Gaussian against `(z/|z|) ^ N |z| ^ (2t)`,
for Lebesgue measure: `∫ F χ |z| ^ (2 (s - 1)) = (π / 2) b ^ (-w) Γ_ℂ(w)`, `w = s + t + |N|/2`. -/
theorem integral_complexGaussian_mul_complexCharFun {b : ℝ} (hb : 0 < b) (N : ℤ) (t s : ℂ)
    (hs : 0 < (s + t + N.natAbs / 2).re) :
    ∫ z : ℂ, complexGaussian b N z * complexCharFun N t z * ((‖z‖ : ℝ) : ℂ) ^ (2 * (s - 1)) =
      (π / 2 : ℂ) * (b : ℂ) ^ (-(s + t + N.natAbs / 2)) * Gammaℂ (s + t + N.natAbs / 2) := by
  set w := s + t + (N.natAbs : ℂ) / 2 with hw
  have hw2 : 0 < (2 * w).re := by
    rw [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have key := integral_norm_cpow_mul_exp_neg_mul_sq (E := ℂ) volume hw2
    (by positivity : 0 < 2 * π * b)
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat] at key
  have hball : volume.real (Metric.ball (0 : ℂ) 1) = π := by
    simp [Measure.real]
  rw [hball] at key
  have hae : (fun z : ℂ => complexGaussian b N z * complexCharFun N t z *
      ((‖z‖ : ℝ) : ℂ) ^ (2 * (s - 1))) =ᵐ[volume] fun z =>
        ((‖z‖ : ℝ) : ℂ) ^ (2 * w - 2) *
          cexp (-(((2 * π * b : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz
    have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
    rw [complexGaussian_mul_complexCharFun hz, mul_right_comm, ← cpow_add _ _ hr]
    congr 1
    · congr 1
      rw [hw]
      ring
    · push_cast; ring
  have hpb : ((2 * π * b : ℝ) : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  rw [integral_congr_ae hae, key, Gammaℂ_def, show 2 * w / 2 = w by ring, one_div,
    inv_cpow _ _ hpb, ← cpow_neg,
    show ((2 * π * b : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) * (b : ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg (by positivity) hb.le]
  push_cast
  ring

end ComplexPlace

end Langlands.Global.Hecke
