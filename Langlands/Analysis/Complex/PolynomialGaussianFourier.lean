import Langlands.Analysis.SchwartzGaussian
import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! # Fourier transformation of polynomial Gaussians -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped FourierTransform InnerProductSpace LineDeriv SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.PolynomialGaussianFourier

open Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial
  (eval_hasTemperateGrowth radialGaussian)

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (u : ι → E)

/-- The real inner products with the selected coordinate vectors, viewed as complex numbers. -/
def coordinates (x : E) (i : ι) : ℂ := (⟪x, u i⟫_ℝ : ℂ)

/-- The Gaussian of scale `b` on a real inner product space, viewed as a complex function. -/
def gaussian (b : ℝ) (x : E) : ℂ := (Real.exp (-(b * ‖x‖ ^ 2)) : ℂ)

private def gaussianSchwartz (b : ℝ) (hb : 0 < b) : 𝓢(E, ℂ) :=
  let e := (LinearEquiv.smulOfNeZero ℝ E (Real.sqrt b) (Real.sqrt_pos.2 hb).ne').toContinuousLinearEquiv
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (radialGaussian.postcompCLM Complex.ofRealCLM)

private theorem gaussianSchwartz_apply (b : ℝ) (hb : 0 < b) (x : E) :
    gaussianSchwartz b hb x = gaussian b x := by
  change (Real.exp (-‖Real.sqrt b • x‖ ^ 2) : ℂ) = _
  rw [gaussian, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hb.le]

omit [FiniteDimensional ℝ E] in
private theorem eval_temperate (p : MvPolynomial ι ℂ) :
    (fun x => eval (coordinates u x) p).HasTemperateGrowth :=
  eval_hasTemperateGrowth (fun i => Complex.ofRealCLM.comp ((innerSL ℝ).flip (u i))) p

private def gaussianPolynomial (b : ℝ) (hb : 0 < b) (p : MvPolynomial ι ℂ) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => eval (coordinates u x) p) (gaussianSchwartz b hb)

private theorem gaussianPolynomial_apply (b : ℝ) (hb : 0 < b) (p : MvPolynomial ι ℂ) (x : E) :
    gaussianPolynomial u b hb p x = eval (coordinates u x) p * gaussian b x := by
  rw [gaussianPolynomial, SchwartzMap.smulLeftCLM_apply_apply (eval_temperate u p), smul_eq_mul,
    gaussianSchwartz_apply]

omit [FiniteDimensional ℝ E] in
private theorem hasDerivAt_coordinates (x y : E) (i : ι) :
    HasDerivAt (fun t : ℝ => coordinates u (x + t • y) i) (coordinates u y i) 0 := by
  have he : (fun t : ℝ => coordinates u (x + t • y) i) = fun t : ℝ =>
      coordinates u x i + (t : ℂ) * coordinates u y i := by
    funext t
    simp only [coordinates, inner_add_left, real_inner_smul_left, Complex.ofReal_add, Complex.ofReal_mul]
  rw [he]
  simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (coordinates u y i)).const_add
    (coordinates u x i)

omit [FiniteDimensional ℝ E] in
private theorem exists_deriv_polynomial (p : MvPolynomial ι ℂ) (y : E) :
    ∃ q : MvPolynomial ι ℂ, ∀ x : E,
      HasDerivAt (fun t : ℝ => eval (coordinates u (x + t • y)) p) (eval (coordinates u x) q) 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, fun _ => by simpa using (hasDerivAt_const (0 : ℝ) c)⟩
  | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      refine ⟨p' + q', fun x => ?_⟩
      convert (hp' x).add (hq' x) using 1
      · ext t
        exact map_add (eval (coordinates u (x + t • y))) p q
      · exact map_add (eval (coordinates u x)) p' q'
  | mul_X p i hp =>
      obtain ⟨q, hq⟩ := hp
      refine ⟨q * X i + p * C (coordinates u y i), fun x => ?_⟩
      convert (hq x).mul (hasDerivAt_coordinates u x y i) using 1
      · ext t
        simp only [map_mul, eval_X, Pi.mul_apply]
      · simp only [map_add, map_mul, eval_X, eval_C, zero_smul, add_zero]

omit [FiniteDimensional ℝ E] in
private theorem hasDerivAt_gaussian (b : ℝ) (x y : E) :
    HasDerivAt (fun t : ℝ => gaussian b (x + t • y))
      ((-2 * (b : ℂ) * (⟪x, y⟫_ℝ : ℂ)) * gaussian b x) 0 := by
  have hnorm : (fun t : ℝ => ‖x + t • y‖ ^ 2) = fun t => ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ * t + ‖y‖ ^ 2 * t ^ 2 := by
    funext t
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm y x]
    ring
  have hn : HasDerivAt (fun t : ℝ => ‖x + t • y‖ ^ 2) (2 * ⟪x, y⟫_ℝ) 0 := by
    rw [hnorm]
    have h := hasDerivAt_id (0 : ℝ)
    convert ((h.const_mul (2 * ⟪x, y⟫_ℝ)).const_add (‖x‖ ^ 2)).add
      ((h.pow 2).const_mul (‖y‖ ^ 2)) using 1
    · rfl
    · norm_num
  have he := ((hn.const_mul b).neg.exp).ofReal_comp
  convert he using 1
  · rfl
  · change _ = ((Real.exp (-(b * ‖x + (0 : ℝ) • y‖ ^ 2)) *
      -(b * (2 * ⟪x, y⟫_ℝ)) : ℝ) : ℂ)
    rw [zero_smul, add_zero, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    unfold gaussian
    ring

omit [FiniteDimensional ℝ E] in
private theorem exists_lineDeriv_polynomial (b : ℝ) (q : MvPolynomial ι ℂ) (i : ι) :
    ∃ q' : MvPolynomial ι ℂ, ∀ x : E,
      HasDerivAt (fun t : ℝ => eval (coordinates u (x + t • u i)) q * gaussian b (x + t • u i))
        (eval (coordinates u x) q' * gaussian b x) 0 := by
  obtain ⟨qd, hqd⟩ := exists_deriv_polynomial u q (u i)
  refine ⟨qd + q * C (-2 * (b : ℂ)) * X i, fun x => ?_⟩
  convert (hqd x).mul (hasDerivAt_gaussian b x (u i)) using 1
  simp only [map_add, map_mul, eval_C, eval_X, zero_smul, add_zero, coordinates]
  ring

variable [MeasurableSpace E] [BorelSpace E]

/-- Fourier transformation of a polynomial in real inner-product coordinates times a Gaussian
produces another polynomial in the same coordinates times the reciprocal-scale Gaussian. -/
theorem exists_polynomial_fourier (b : ℝ) (hb : 0 < b) (Φ : 𝓢(E, ℂ)) (p : MvPolynomial ι ℂ)
    (hΦ : ∀ x, Φ x = eval (coordinates u x) p * gaussian b x) :
    ∃ q : MvPolynomial ι ℂ, ∀ x,
      (𝓕 Φ) x = eval (coordinates u x) q * gaussian ((Real.pi ^ 2) / b) x := by
  have hΦeq : Φ = gaussianPolynomial u b hb p := by
    ext x
    rw [hΦ, gaussianPolynomial_apply]
  rw [hΦeq]
  clear Φ hΦ hΦeq
  let B := gaussianPolynomial u b hb
  let b' : ℝ := Real.pi ^ 2 / b
  let δ : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)
  have hδ : δ ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  change ∃ q : MvPolynomial ι ℂ, ∀ x, (𝓕 (B p)) x = eval (coordinates u x) q * gaussian b' x
  induction p using MvPolynomial.induction_on with
  | C c =>
      have hB : B (C c) = c • gaussianSchwartz b hb := by
        ext x
        simp [B, gaussianPolynomial_apply, gaussianSchwartz_apply, smul_eq_mul]
      let K : ℂ := ((Real.pi : ℂ) / (b : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
      refine ⟨C (c * K), fun x => ?_⟩
      rw [hB, FourierSMul.fourier_smul, smul_apply, smul_eq_mul]
      have hfunction : (gaussianSchwartz b hb : E → ℂ) = fun x => Complex.exp (-b * ‖x‖ ^ 2) := by
        funext x
        rw [gaussianSchwartz_apply, gaussian, Complex.ofReal_exp]
        push_cast
        rw [neg_mul]
      rw [congrFun (SchwartzMap.fourier_coe (gaussianSchwartz b hb)) x,
        hfunction, fourier_gaussian_innerProductSpace (by simpa : 0 < (b : ℂ).re),
        eval_C, gaussian, Complex.ofReal_exp]
      dsimp only [K, b']
      push_cast
      rw [← mul_assoc]
      congr 2
      ring
  | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      have hB : B (p + q) = B p + B q := by
        ext x
        simp [B, gaussianPolynomial_apply, add_mul]
      refine ⟨p' + q', fun x => ?_⟩
      rw [hB, FourierAdd.fourier_add, add_apply, hp', hq', map_add, add_mul]
  | mul_X p i hp =>
      obtain ⟨q, hq⟩ := hp
      obtain ⟨q', hq'⟩ := exists_lineDeriv_polynomial u b' q i
      let L := SchwartzMap.smulLeftCLM ℂ (fun x : E => ⟪x, u i⟫_ℝ) (B p)
      have hL : L = B (p * X i) := by
        ext x
        rw [show L x = ⟪x, u i⟫_ℝ • B p x from
          SchwartzMap.smulLeftCLM_apply_apply ((innerSL ℝ).flip (u i)).hasTemperateGrowth (B p) x]
        simp [B, gaussianPolynomial_apply, Complex.real_smul, coordinates]
        ring
      have hF : ∂_{u i} (𝓕 (B p)) = δ • 𝓕 (B (p * X i)) := by
        rw [SchwartzMap.lineDerivOp_fourier_eq, ← hL, FourierSMul.fourier_smul]
      refine ⟨C δ⁻¹ * q', fun x => ?_⟩
      have hD : (∂_{u i} (𝓕 (B p))) x = eval (coordinates u x) q' * gaussian b' x := by
        rw [SchwartzMap.lineDerivOp_apply]
        have he : HasLineDerivAt ℝ (⇑(𝓕 (B p) : 𝓢(E, ℂ)))
            (eval (coordinates u x) q' * gaussian b' x) x (u i) := by
          change HasDerivAt (fun t : ℝ => (𝓕 (B p)) (x + t • u i)) _ 0
          simpa only [hq] using hq' x
        exact he.lineDeriv
      rw [hF, smul_apply, smul_eq_mul] at hD
      rw [map_mul, eval_C, mul_assoc, ← hD, ← mul_assoc, inv_mul_cancel₀ hδ, one_mul]

end Langlands.Analysis.PolynomialGaussianFourier
