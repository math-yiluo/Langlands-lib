import Langlands.Global.AdelicCoordinatePolynomialFourier
import Langlands.Analysis.SchwartzCompactFamilies

/-! # Fourier boundary values with varying compact spectral coefficients -/

noncomputable section

open Filter MeasureTheory Set
open scoped Classical ContDiff ENNReal FourierTransform InnerProductSpace SchwartzMap Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Analysis

variable {ι : Type*} [Fintype ι]

local notation "τ" => (2 * Real.pi)
local notation "U" => (ι → ℝ)
local notation "V" => EuclideanSpace ℝ ι

private theorem twoPi_pos : 0 < τ := mul_pos (by norm_num) Real.pi_pos

private def coordinateEquiv : V ≃L[ℝ] U :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)

private def unscaleCoordinates : U ≃L[ℝ] V :=
  coordinateEquiv.symm.trans
    (LinearEquiv.smulOfNeZero ℝ V (-τ) (neg_ne_zero.mpr twoPi_pos.ne')).toContinuousLinearEquiv.symm

private theorem scaled_unscaleCoordinates (x : U) :
    WithLp.ofLp ((-τ) • unscaleCoordinates x) = x := by
  change coordinateEquiv
    ((LinearEquiv.smulOfNeZero ℝ V (-τ) (neg_ne_zero.mpr twoPi_pos.ne')).toContinuousLinearEquiv
      (unscaleCoordinates x)) = x
  simp only [unscaleCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]

private def reflectedPolynomial (P : MvPolynomial ι ℂ) (x : U) : ℂ :=
  MvPolynomial.eval (fun i => -(x i : ℂ)) P

private theorem exp_displaced_sum (d : U) (t : ℝ) (x y : U) :
    Complex.exp (∑ i, -displacedOrthantParameter d t y i * (x i : ℂ)) =
      (Real.exp (-(t * ∑ i, d i * x i)) : ℂ) * coordinateFourierPhase x y := by
  rw [Complex.ofReal_exp, coordinateFourierPhase, ← Complex.exp_add]
  congr 1
  simp only [displacedOrthantParameter]
  push_cast
  rw [← neg_mul, mul_neg, ← neg_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Positive displacement makes the spectral test of a regularized orthant term integrable.
Fubini gives the integral of the polynomial Fourier test with the corresponding spatial
damping. -/
theorem regularizedOrthantTerm_integrable_integral (d b : U) (hd : ∀ i, d i ≠ 0)
    (P : MvPolynomial ι ℂ) {ν : Measure U} [SFinite ν] {f : U → ℂ}
    (hf : Integrable f ν) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => regularizedOrthantTerm b P (displacedOrthantParameter d t y) * f y) ν ∧
      orthantSign d * (∫ y, regularizedOrthantTerm b P (displacedOrthantParameter d t y) * f y ∂ν) =
        ∫ x in translatedOrientedOrthant d b,
          Real.exp (-(t * ∑ i, d i * x i)) • orthantPolynomialTest ν f P x := by
  let μ : Measure U := volume.restrict (translatedOrientedOrthant d b)
  let w (x : U) := Real.exp (-(t * ∑ i, d i * x i)) • reflectedPolynomial P x
  have hReal (y : U) (i : ι) : (displacedOrthantParameter d t y i).re = t * d i := by
    simp [displacedOrthantParameter, Complex.mul_re]
  have hLaplace (y : U) := translatedOrthant_polynomialLaplace
    (d := d) (z := displacedOrthantParameter d t y)
    (fun i => by rw [hReal]; exact mul_ne_zero ht.ne' (hd i))
    (fun i => by rw [hReal]; exact mul_pos_iff_of_pos_left ht) b P
  have hFactor (x y : U) :
      Complex.exp (∑ i, -displacedOrthantParameter d t y i * (x i : ℂ)) *
          reflectedPolynomial P x = w x * coordinateFourierPhase x y := by
    dsimp only [w]
    rw [exp_displaced_sum, Complex.real_smul, mul_right_comm]
  have hw : Integrable w μ := by
    have hOne (x : U) : coordinateFourierPhase x 0 = 1 := by simp [coordinateFourierPhase]
    have h := (hLaplace 0).1
    change Integrable (fun x => Complex.exp (∑ i, -displacedOrthantParameter d t 0 i *
      (x i : ℂ)) * reflectedPolynomial P x) μ at h
    simpa only [hFactor, hOne, mul_one] using h
  let g (x y : U) := w x * (coordinateFourierPhase x y * f y)
  have hPhase : Continuous (fun p : U × U => coordinateFourierPhase p.1 p.2) := by
    unfold coordinateFourierPhase
    fun_prop
  have hg : Integrable (Function.uncurry g) (μ.prod ν) := by
    refine (hw.mul_prod hf).mono
      (hw.aestronglyMeasurable.comp_fst.mul
        (hPhase.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)) (ae_of_all _ fun p => ?_)
    change ‖g p.1 p.2‖ ≤ ‖w p.1 * f p.2‖
    have hNorm : ‖coordinateFourierPhase p.1 p.2‖ = 1 := Complex.norm_exp_I_mul_ofReal _
    simp only [g, norm_mul, hNorm, one_mul, le_refl]
  have hInner (y : U) :
      orthantSign d * (regularizedOrthantTerm b P (displacedOrthantParameter d t y) * f y) =
        ∫ x, g x y ∂μ := by
    simp_rw [g, ← mul_assoc, ← hFactor, integral_mul_const]
    exact congrArg (fun z : ℂ => z * f y) (hLaplace y).2
  have hs : orthantSign d ≠ 0 := by
    unfold orthantSign
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · have h := hg.integral_prod_right.congr (ae_of_all _ fun y => (hInner y).symm)
    simpa only [← mul_assoc, inv_mul_cancel₀ hs, one_mul] using h.const_mul (orthantSign d)⁻¹
  calc
    _ = ∫ y, (∫ x, g x y ∂μ) ∂ν := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ hInner)
    _ = ∫ x, (∫ y, g x y ∂ν) ∂μ := (integral_integral_swap hg).symm
    _ = _ := by
      simp_rw [g, integral_const_mul, orthantPolynomialTest, w, Complex.real_smul, mul_assoc]
      rfl

private theorem reflectedPolynomial_growth (P : MvPolynomial ι ℂ) :
    (reflectedPolynomial P).HasTemperateGrowth := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [show reflectedPolynomial (MvPolynomial.C c) = fun _ => c from
        funext fun _ => MvPolynomial.eval_C c]
      exact Function.HasTemperateGrowth.const c
  | add P Q hP hQ =>
      rw [show reflectedPolynomial (P + Q) = reflectedPolynomial P + reflectedPolynomial Q from
        funext fun _ => MvPolynomial.eval_add]
      exact hP.add hQ
  | mul_X P i hP =>
      let L := -(Complex.ofRealCLM.comp (ContinuousLinearMap.proj (φ := fun _ : ι => ℝ) i))
      rw [show reflectedPolynomial (P * MvPolynomial.X i) = reflectedPolynomial P * ⇑L from by
        funext x
        change MvPolynomial.eval (fun j => -(x j : ℂ)) (P * MvPolynomial.X i) =
          MvPolynomial.eval (fun j => -(x j : ℂ)) P * -(x i : ℂ)
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]]
      exact hP.mul L.hasTemperateGrowth

private def polynomialFourierSchwartz (P : MvPolynomial ι ℂ) (a : 𝓢(U, ℂ)) : 𝓢(U, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (reflectedPolynomial P) <|
    (τ⁻¹ ^ Fintype.card ι : ℝ) •
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ unscaleCoordinates
        (𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinateEquiv a))

private theorem orthantFourierTest_neg_scaled_schwartz (B : 𝓢(V, ℂ)) (x : V) :
    orthantFourierTest (coordinateSpectralMeasure ι) (fun z => B (WithLp.toLp 2 z))
        (WithLp.ofLp ((-τ) • x)) = τ⁻¹ ^ Fintype.card ι • (𝓕⁻ B) x := by
  rw [orthantFourierTest, coordinateSpectralMeasure, integral_smul_measure, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal twoPi_pos.le, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  rw [← (PiLp.volume_preserving_ofLp ι).integral_comp
    (coordinateEquiv (ι := ι)).toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change coordinateFourierPhase (WithLp.ofLp ((-τ) • x)) z.ofLp * B z =
      Complex.exp (((τ * ⟪(z : V), x⟫_ℝ : ℝ) : ℂ) * Complex.I) * B z
    have hInner : ⟪(z : V), x⟫_ℝ = ∑ i, x i * z i := by
      rw [PiLp.inner_apply]
      simp
    have hDot : -(∑ i, (WithLp.ofLp ((-τ) • x)) i * z.ofLp i) = τ * ⟪(z : V), x⟫_ℝ := by
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hInner, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [coordinateFourierPhase, hDot, mul_comm Complex.I]

private theorem polynomialFourierSchwartz_apply (P : MvPolynomial ι ℂ) (a : 𝓢(U, ℂ)) (x : U) :
    polynomialFourierSchwartz P a x = orthantPolynomialTest (coordinateSpectralMeasure ι) a P x := by
  rw [polynomialFourierSchwartz, SchwartzMap.smulLeftCLM_apply_apply (reflectedPolynomial_growth P)]
  let B := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinateEquiv a
  change reflectedPolynomial P x * (τ⁻¹ ^ Fintype.card ι : ℝ) • (𝓕⁻ B) (unscaleCoordinates x) = _
  rw [← orthantFourierTest_neg_scaled_schwartz, scaled_unscaleCoordinates]
  rfl

private theorem continuous_polynomialFourierSchwartz (P : MvPolynomial ι ℂ) :
    Continuous (polynomialFourierSchwartz P) := by
  unfold polynomialFourierSchwartz
  fun_prop

private theorem integrable_coordinateSpectralMeasure (a : 𝓢(U, ℂ)) :
    Integrable a (coordinateSpectralMeasure ι) := by
  have h : (ENNReal.ofReal τ)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr twoPi_pos).ne'
  exact a.integrable.smul_measure (ENNReal.pow_ne_top h)

private theorem tendsto_integral_damped_schwartz (s : Set U) (D : U → ℝ)
    (hD : Measurable D) (hDpos : ∀ᵐ x ∂volume.restrict s, 0 ≤ D x)
    (g : ℝ → 𝓢(U, ℂ)) (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0))) :
    Tendsto (fun t : ℝ => ∫ x in s, Real.exp (-(t * D x)) • g t x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in s, g 0 x)) := by
  let μ : Measure U := volume.restrict s
  let w (t : ℝ) (x : U) := Real.exp (-(t * D x))
  have hbound {t : ℝ} (ht : 0 < t) : ∀ᵐ x ∂μ, ‖w t x‖ ≤ 1 := by
    filter_upwards [hDpos] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht.le hx))
  have hInt {t : ℝ} (ht : 0 < t) (a : 𝓢(U, ℂ)) :
      Integrable (fun x => w t x • a x) μ := by
    refine (a.integrable (μ := volume)).restrict.mono ?_ ?_
    · exact (Real.continuous_exp.measurable.comp ((hD.const_mul t).neg)).aestronglyMeasurable.smul
        a.continuous.aestronglyMeasurable
    · filter_upwards [hbound ht] with x hx
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
  have hL1 : Tendsto (fun t => ∫ x : U, ‖(g t - g 0) x‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hDiff : Tendsto (fun t => g t - g 0) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [sub_self] using hg.sub (tendsto_const_nhds (x := g 0))
    let L := SchwartzMap.toLpCLM ℝ ℂ 1 (volume : Measure U)
    have h := (L.continuous.continuousAt.tendsto.comp hDiff).norm
    simpa only [L, Function.comp_apply, map_zero, norm_zero, SchwartzMap.toLpCLM_apply,
      SchwartzMap.norm_toLp_one] using h
  have hChange : Tendsto (fun t : ℝ => ∫ x, w t x • (g t - g 0) x ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hL1
    filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with t ht
    calc
      ‖∫ x, w t x • (g t - g 0) x ∂μ‖ ≤ ∫ x, ‖w t x • (g t - g 0) x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖(g t - g 0) x‖ ∂μ := by
        apply integral_mono_ae (hInt ht (g t - g 0)).norm (g t - g 0).integrable.norm.restrict
        filter_upwards [hbound ht] with x hx
        rw [norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) hx
      _ ≤ ∫ x : U, ‖(g t - g 0) x‖ :=
        setIntegral_le_integral (g t - g 0).integrable.norm (ae_of_all _ fun _ => norm_nonneg _)
  have hFixed := tendsto_integral_remove_exponential_damping hD.aemeasurable hDpos
    (g 0).integrable.restrict
  have hSum := hChange.add hFixed
  rw [zero_add] at hSum
  refine hSum.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with t ht
  rw [← integral_add (hInt ht (g t - g 0)) (hInt ht (g 0))]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change w t x • (g t - g 0) x + w t x • g 0 x = w t x • g t x
    rw [← smul_add, ← add_apply, sub_add_cancel]

/-- A variable spectral Schwartz test converging at zero has the signed boundary value obtained
by testing the translated oriented cone against the limiting polynomial Fourier test. -/
def RegularizedOrthantVaryingTestStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] (d b : ι → ℝ) (P : MvPolynomial ι ℂ)
    (a : ℝ → 𝓢((ι → ℝ), ℂ)), (∀ i, d i ≠ 0) →
    Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 (a 0)) →
    Tendsto (fun t : ℝ => orthantSign d *
      (∫ y, regularizedOrthantTerm b P (displacedOrthantParameter d t y) * a t y
        ∂coordinateSpectralMeasure ι)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in translatedOrientedOrthant d b,
        orthantPolynomialTest (coordinateSpectralMeasure ι) (a 0) P x))

theorem regularizedOrthantVaryingTest : RegularizedOrthantVaryingTestStatement := by
  intro ι _ d b P a hd ha
  let s := translatedOrientedOrthant d b
  let D (x : ι → ℝ) := ∑ i, d i * (x i + b i)
  let c := ∑ i, d i * b i
  let g (t : ℝ) := polynomialFourierSchwartz P (a t)
  have hs : MeasurableSet s := (measurable_id.add_const b) (measurableSet_orientedOrthant d)
  have hD : Measurable D := by unfold D; fun_prop
  have hDpos : ∀ᵐ x ∂volume.restrict s, 0 ≤ D x := by
    filter_upwards [ae_restrict_mem hs] with x hx
    refine Finset.sum_nonneg fun i _ => ?_
    have hi : x i + b i ∈ (if 0 < d i then Ioi 0 else Iio 0) := hx i (mem_univ i)
    split_ifs at hi with h
    · exact mul_nonneg h.le (show 0 < x i + b i from hi).le
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt h) (show x i + b i < 0 from hi).le
  have hc : Tendsto (fun t : ℝ => Real.exp (t * c)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : Continuous (fun t : ℝ => Real.exp (t * c)) := by fun_prop
    simpa only [ContinuousWithinAt, zero_mul, Real.exp_zero] using
      h.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)
  have hlim := hc.smul (tendsto_integral_damped_schwartz s D hD hDpos g
    ((continuous_polynomialFourierSchwartz P).continuousAt.tendsto.comp ha))
  rw [one_smul] at hlim
  simp_rw [g, polynomialFourierSchwartz_apply] at hlim
  have : SFinite (coordinateSpectralMeasure ι) := by unfold coordinateSpectralMeasure; infer_instance
  refine hlim.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with t ht
  rw [(regularizedOrthantTerm_integrable_integral d b hd P (integrable_coordinateSpectralMeasure (a t)) ht).2,
    ← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [smul_smul, ← Real.exp_add]
    have hx : D x = (∑ i, d i * x i) + c := by unfold D c; simp [mul_add, Finset.sum_add_distrib]
    rw [hx]
    apply congrArg (fun r : ℝ => Real.exp r • _)
    ring

/-- Joint smoothness and common compact spectral support suffice for the varying-test boundary
value. The boundary uses the coefficient at zero displacement. -/
theorem regularizedOrthantFourierBoundary_compactFamily (d b : U) (hd : ∀ i, d i ≠ 0)
    (P : MvPolynomial ι ℂ) (a : ℝ × U → ℂ) (ha : ContDiff ℝ ∞ a) (S : Set U) (hS : IsCompact S)
    (hs : ∀ t y, y ∉ S → a (t, y) = 0) :
    Tendsto (fun t : ℝ => orthantSign d *
      (∫ y, regularizedOrthantTerm b P (displacedOrthantParameter d t y) * a (t, y)
        ∂coordinateSpectralMeasure ι)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in translatedOrientedOrthant d b,
        orthantPolynomialTest (coordinateSpectralMeasure ι) (fun y => a (0, y)) P x)) := by
  let A (t : ℝ) := SchwartzCompactFamilies.ofCompactSupport (fun y => a (t, y))
    (ha.comp (contDiff_const.prodMk contDiff_id)) S hS (hs t)
  have hA : Continuous A :=
    SchwartzCompactFamilies.schwartzCompactFamilyContinuity ℝ U ℂ A S hS hs ha
  exact regularizedOrthantVaryingTest d b P A hd hA.continuousWithinAt

/-- In the second limit the vertex advances in a strictly positive coroot direction.
The all-positive orientation gives the local polynomial distribution at the frequency shift.
Every orientation with a negative slope gives zero. -/
theorem translatedOrthant_compactTest_tendsto (d b v ξ : U) (hd : ∀ i, d i ≠ 0)
    (hv : ∀ i, 0 < v i) (P : MvPolynomial ι ℂ) (a : U → ℂ)
    (ha : ContDiff ℝ ∞ a) (hs : HasCompactSupport a) :
    Tendsto (fun n : ℕ => ∫ x in translatedOrientedOrthant d (b + (n : ℝ) • v),
      orthantPolynomialTest (coordinateSpectralMeasure ι) (fun y => a (y + ξ)) P x) atTop
      (𝓝 (if ∀ i, 0 < d i then coordinatePolynomialPointEvaluation P ξ a else 0)) := by
  have h := (coordinatePolynomialFourierEvaluation P ξ).2.1 a ha hs
  rw [← h.2]
  exact translatedOrthant_polynomialTest_tendsto d b v hd hv (coordinateSpectralMeasure ι)
    (fun y => a (y + ξ)) P h.1

end Langlands.Global
