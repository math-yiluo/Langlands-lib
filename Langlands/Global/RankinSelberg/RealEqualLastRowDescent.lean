import Langlands.Global.RankinSelberg.RealUnequalLastRowDescent
import Langlands.Global.RankinSelberg.RealEqualConvergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Last-row descent for real equal-rank integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealEqualLastRowDescent

open ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open RealUnequalFamily (HasLeftCharacter HasUniformGauge ordinary_halfPlaneDomination
  continuous_integrand integrand_mk)
open RealUnequalLastRowDescent (lastRowQ lastRowQ_mk continuous_lastRowQ lastRowFactor
  continuous_lastRowFactor lastRowFactor_zero_one lowerBlockPair_eq logDet_lastRowFactor
  hasLeftCharacter_translate hasLeftCharacter_pad hasUniformGauge_translate
  hasUniformGauge_pad_translate eq_zero_on_right unitsExtend2
  unitsExtend2_val eq_zero_of_fourier_units_eq_zero sigmaFinite_measure)
open RealWhittakerTranslatedMellin (HasGaugeBound)
open RealLowerBlockChart (lastRowChart lastRowMeasure lastRowChart_integral
  quotientDensity rowEquiv unitsLower)
open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs)
open RealEqualConvergence (kernel logDet realEqualIntegrand_eq realWhittakerCharacter_mul_neg
  exists_convergence hasRapidDecay_schwartz)
open RealConvergenceAnalysis (norm_cexp_mul_ofReal differentiableOn_integral_cexp_mul)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel RealRankZero.unitsMeasurable RealRankZero.unitsBorel

variable {n : ℕ}

private abbrev G (k : ℕ) := Langlands.GeneralLinear (k + 1) ℝ
private abbrev Q (k : ℕ) := LeftUnipotentQuotient k ℝ
local notation "Row" => (Fin (n + 1 + 1) → ℝ)
local notation "X" => (Fin (n + 1) → ℝ) × ℝˣ
local notation "pad" => padGL (Nat.le_succ (n + 1))

private theorem invariant_product {a : ℝˣ} {W V : G (n + 1) → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) :
    ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1 + 1) ℝ, ∀ g,
      W (u * g) * V (u * g) = W g * V g := by
  intro u hu g
  rw [hW u hu g, hV u hu g, mul_mul_mul_comm, realWhittakerCharacter_mul_neg, one_mul]

private theorem continuous_quotient_logDet : Continuous (fun q : Q (n + 1) => logDet q.out) := by
  rw [show (fun q : Q (n + 1) => logDet q.out) = _ from funext fun q =>
    RealEqualConvergence.out_eq_descend logDet RealEqualConvergence.logDet_unipotent_mul q]
  exact RealEqualConvergence.continuous_descend_real
    RealEqualConvergence.logDet_unipotent_mul RealEqualConvergence.continuous_logDet

private theorem continuous_quotient_kernel {a : ℝˣ} {W V : G (n + 1) → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) {Φ : Row → ℂ} (hΦ : Continuous Φ) :
    Continuous (fun q : Q (n + 1) => RealEqualConvergence.kernel W V Φ q.out) := by
  have h := RealEqualConvergence.kernel_unipotent_mul (Φ := Φ) (invariant_product hW hV)
  rw [show (fun q : Q (n + 1) => RealEqualConvergence.kernel W V Φ q.out) = _ from
    funext fun q => RealEqualConvergence.out_eq_descend _ h q]
  exact RealEqualConvergence.continuous_descend h
    (RealEqualConvergence.continuous_kernel hWc hVc hΦ)

private theorem integrand_mk_eq {a : ℝˣ} {W V : G (n + 1) → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (Φ : Row → ℂ)
    (s : ℂ) (g : G (n + 1)) :
    realEqualIntegrand W V Φ s (Quotient.mk _ g) =
      W g * V g * Φ (Langlands.RankinSelberg.lastRow g) * Complex.exp (s * (logDet g : ℂ)) := by
  rw [realEqualIntegrand_eq]
  dsimp only
  rw [RealEqualConvergence.out_eq_descend _
      (RealEqualConvergence.kernel_unipotent_mul (invariant_product hW hV)),
    RealEqualConvergence.out_eq_descend _ RealEqualConvergence.logDet_unipotent_mul]
  rfl

private def phase (y : Row) (x : Row) : ℂ := Real.fourierChar (∑ j, x j * y j)

private theorem smooth_phase (y : Row) : ContDiff ℝ (∞ : ℕ∞ω) (phase y) := by
  unfold phase
  simp only [Real.fourierChar_apply]
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (ContDiff.sum fun j _ =>
      (contDiff_apply ℝ (fun _ : Fin (n + 1 + 1) => ℝ) j).mul contDiff_const))).mul contDiff_const)

private def rowBump (n : ℕ) : ContDiffBump (Fin.snoc (α := fun _ => ℝ) (0 : Fin (n + 1) → ℝ) 1) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

private def test (y : Row) : SchwartzMap Row ℂ :=
  have hcompact : HasCompactSupport (fun x => ((rowBump n x : ℝ) : ℂ)) :=
    (rowBump n).hasCompactSupport.comp_left Complex.ofReal_zero
  (hcompact.mul_right (f' := phase y)).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp (rowBump n).contDiff).mul (smooth_phase y))

private theorem test_apply (y x : Row) : test y x = (rowBump n x : ℂ) * phase y x := rfl

private theorem phase_zero (x : Row) : phase 0 x = 1 := by
  simp [phase]

private theorem test_modulate (y x : Row) : test y x = phase y x * test 0 x := by
  rw [test_apply, test_apply, phase_zero, mul_one, mul_comm]

private theorem chart_lastRow (q : Q n) (x : Fin (n + 1) → ℝ) (u : ℝˣ) :
    lastRowQ (lastRowChart n (q, x, u)) = Fin.snoc (α := fun _ => ℝ) x (u : ℝ) := by
  induction q using Quotient.inductionOn with
  | h g =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Langlands.GeneralLinear.lowerBlockPair g (rowEquiv x) (unitsLower u)
        (Fin.natAdd (n + 1) (0 : Fin 1)) (Fin.natAdd (n + 1) (0 : Fin 1)) = _
      rw [Langlands.GeneralLinear.lowerBlockPair_22, Fin.snoc_last]
      rfl
    · change Langlands.GeneralLinear.lowerBlockPair g (rowEquiv x) (unitsLower u)
        (Fin.natAdd (n + 1) (0 : Fin 1)) (Fin.castAdd 1 j) = _
      rw [Langlands.GeneralLinear.lowerBlockPair_21, Fin.snoc_castSucc]
      rfl

private theorem continuous_row : Continuous (fun p : X => Fin.snoc (α := fun _ => ℝ) p.1 (p.2 : ℝ)) := by
  refine continuous_pi fun i => Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact Units.continuous_val.comp continuous_snd
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_fst

private theorem continuousAt_smallerIntegral (D : RealQuotientMeasureData n)
    {a : ℝˣ} {W V : G (n + 1) → ℂ} (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) (hWg : HasGaugeBound W) (hVg : HasGaugeBound V) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ContinuousAt (fun L : G (n + 1) =>
      realUnequalIntegral (Nat.lt_succ_self n) D (fun z => W (z * L))
        (fun z => V (pad z * L)) s) 1 := by
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : G (n + 1))
  let S : Set (G (n + 1) × ℂ) := K ×ˢ univ
  let Wf : G (n + 1) × ℂ → G (n + 1) → ℂ := fun p z => W (z * p.1)
  let Vf : G (n + 1) × ℂ → G n → ℂ := fun p z => V (pad z * p.1)
  have hWl (p : G (n + 1) × ℂ) : HasLeftCharacter a (Wf p) := hasLeftCharacter_translate hW p.1
  have hVl (p : G (n + 1) × ℂ) : HasLeftCharacter (-a) (Vf p) :=
    hasLeftCharacter_pad (hasLeftCharacter_translate hV p.1) _
  have hWb : HasUniformGauge S Wf := hasUniformGauge_translate hWg hKc S Prod.fst (fun _ hp => hp.1)
  have hVb : HasUniformGauge S Vf := hasUniformGauge_pad_translate hVg hKc S Prod.fst (fun _ hp => hp.1)
  obtain ⟨σ, hdom⟩ := ordinary_halfPlaneDomination (Nat.lt_succ_self n) D S Wf Vf Prod.snd
    hWl hVl hWb hVb
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨B, hBi, hB⟩ := hdom s.re
  change ContinuousAt (fun L => ∫ q, realUnequalIntegrand (Nat.lt_succ_self n)
    (Wf (L, s)) (Vf (L, s)) s q ∂D.measure) 1
  refine continuousAt_of_dominated ?_ ?_ hBi ?_
  · exact Eventually.of_forall fun L => (continuous_integrand _ (hWl (L, s)) (hVl (L, s))
      (hWc.comp (continuous_id.mul continuous_const))
      (hVc.comp ((UnequalAnalytic.continuous_padGL _).mul continuous_const)) s).aestronglyMeasurable
  · filter_upwards [hK1] with L hL
    exact ae_of_all _ fun q => hB (L, s) ⟨hL, mem_univ _⟩ hs le_rfl q
  · refine ae_of_all _ fun q => ?_
    change ContinuousAt (fun L => W (pad q.out * L) * V (pad q.out * L) * _) 1
    exact (((hWc.comp (continuous_const.mul continuous_id)).mul
      (hVc.comp (continuous_const.mul continuous_id))).mul continuous_const).continuousAt

private theorem fiber_eq (D : RealQuotientMeasureData n) {a : ℝˣ} {W V : G (n + 1) → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (Φ : Row → ℂ) (s : ℂ) (p : X) :
    (∫ q, realEqualIntegrand W V Φ s (lastRowChart n (q, p.1, p.2))
        ∂(D.measure.withDensity (quotientDensity n))) =
      (Φ (Fin.snoc (α := fun _ => ℝ) p.1 (p.2 : ℝ)) * Complex.exp (s * (Real.log |(p.2 : ℝ)| : ℂ))) *
        realUnequalIntegral (Nat.lt_succ_self n) D (fun z => W (z * lastRowFactor p.1 p.2))
          (fun z => V (pad z * lastRowFactor p.1 p.2)) (s - 1 / 2) := by
  have hf : Measurable fun q : Q n => ((quotientDetAbs q)⁻¹).toNNReal :=
    (continuous_real_toNNReal.comp
      (continuous_quotientDetAbs.inv₀ fun q => (quotientDetAbs_pos q).ne')).measurable
  change ∫ q, _ ∂(D.measure.withDensity fun q => (((quotientDetAbs q)⁻¹).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hf]
  change _ = _ * ∫ q, _ ∂D.measure
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  induction q using Quotient.inductionOn with
  | h g =>
    have hrow := chart_lastRow (Quotient.mk _ g) p.1 p.2
    change Langlands.RankinSelberg.lastRow
      (Langlands.GeneralLinear.lowerBlockPair g (rowEquiv p.1) (unitsLower p.2)) = _ at hrow
    change (((quotientDetAbs (Quotient.mk _ g : Q n))⁻¹).toNNReal : ℝ) •
      realEqualIntegrand W V Φ s (Quotient.mk _ (Langlands.GeneralLinear.lowerBlockPair g
        (rowEquiv p.1) (unitsLower p.2))) = _
    rw [RealLowerBlockChart.quotientDetAbs_mk, Real.coe_toNNReal _ (inv_nonneg.mpr (abs_nonneg _)),
      Complex.real_smul, integrand_mk_eq hW hV, hrow, lowerBlockPair_eq]
    change _ = _ * realUnequalIntegrand (Nat.lt_succ_self n)
      (fun z => W (z * lastRowFactor p.1 p.2)) (fun z => V (pad z * lastRowFactor p.1 p.2))
      (s - 1 / 2) (Quotient.mk _ g)
    rw [integrand_mk _ (hasLeftCharacter_translate hW _) (hasLeftCharacter_pad
      (hasLeftCharacter_translate hV _) _)]
    have hlog : logDet (pad g * lastRowFactor p.1 p.2) = logDet g + Real.log |(p.2 : ℝ)| := by
      rw [← logDet_lastRowFactor p.1 p.2]
      unfold logDet
      rw [Units.val_mul, Matrix.det_mul, UnequalAnalytic.det_padGL, realNormalizedAbs,
        realNormalizedAbs, realNormalizedAbs, abs_mul,
        Real.log_mul (abs_ne_zero.mpr (RealLowerBlockChart.det_ne_zero g))
          (abs_ne_zero.mpr (RealLowerBlockChart.det_ne_zero _))]
    change ((|g.val.det|⁻¹ : ℝ) : ℂ) *
      (W (pad g * lastRowFactor p.1 p.2) * V (pad g * lastRowFactor p.1 p.2) * _ *
        Complex.exp (s * (logDet (pad g * lastRowFactor p.1 p.2) : ℂ))) =
      _ * (W (pad g * lastRowFactor p.1 p.2) * V (pad g * lastRowFactor p.1 p.2) *
        Complex.exp ((s - 1 / 2 - (((n + 1 - n : ℕ) : ℂ)) / 2) * (logDet g : ℂ)))
    have hdet : ((|g.val.det|⁻¹ : ℝ) : ℂ) = Complex.exp (-(logDet g : ℂ)) := by
      rw [logDet, realNormalizedAbs, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
        Real.exp_log (abs_pos.mpr (RealLowerBlockChart.det_ne_zero g))]
    have hsub : n + 1 - n = 1 := by omega
    rw [hdet, hlog, hsub, Nat.cast_one, Complex.ofReal_add]
    rw [show s * ((logDet g : ℂ) + (Real.log |(p.2 : ℝ)| : ℂ)) =
      s * (Real.log |(p.2 : ℝ)| : ℂ) + (s - 1 / 2 - 1 / 2) * (logDet g : ℂ) + (logDet g : ℂ) by ring]
    simp only [Complex.exp_add]
    have hcancel : Complex.exp (-(logDet g : ℂ)) * Complex.exp (logDet g : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination (W (pad g * lastRowFactor p.1 p.2) * V (pad g * lastRowFactor p.1 p.2) *
      Φ (Fin.snoc (α := fun _ => ℝ) p.1 (p.2 : ℝ)) * Complex.exp (s * (Real.log |(p.2 : ℝ)| : ℂ)) *
      Complex.exp ((s - 1 / 2 - 1 / 2) * (logDet g : ℂ))) * hcancel

private theorem integrand_modulate (y : Row) (W V : G (n + 1) → ℂ) (s : ℂ) (q : Q (n + 1)) :
    realEqualIntegrand W V (test y) s q = phase y (lastRowQ q) * realEqualIntegrand W V (test 0) s q := by
  have hq : lastRowQ q = Langlands.RankinSelberg.lastRow q.out := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq, realEqualIntegrand_eq, realEqualIntegrand_eq]
  simp only [kernel, test_modulate y]
  ring

private theorem integrand_modulate_norm (y : Row) (W V : G (n + 1) → ℂ) (s : ℂ) (q : Q (n + 1)) :
    ‖realEqualIntegrand W V (test y) s q‖ = ‖realEqualIntegrand W V (test 0) s q‖ := by
  rw [integrand_modulate, norm_mul, phase, Circle.norm_coe, one_mul]

private theorem gauge_on_iwasawa {W : G (n + 1) → ℂ} (hW : HasGaugeBound W) :
    RealEqualConvergence.HasGauge W := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun y k => ?_⟩
  simpa only [RealIwasawa.alpha_torus_mul_unitary] using hb (RealIwasawa.torus y * k.val)

private theorem equal_quotient_integrand_continuous {a : ℝˣ} {W V : G (n + 1) → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (hWc : Continuous W)
    (hVc : Continuous V) (Φ : SchwartzMap Row ℂ) (s : ℂ) :
    Continuous (realEqualIntegrand W V Φ s) := by
  rw [realEqualIntegrand_eq]
  exact (continuous_quotient_kernel hW hV hWc hVc Φ.continuous).mul
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_quotient_logDet)))

private theorem holomorphic_modulate {a : ℝˣ} {W V : G (n + 1) → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (hWc : Continuous W)
    (hVc : Continuous V) (D : RealQuotientMeasureData (n + 1)) (y : Row) {σ : ℝ}
    (hInt : ∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W V (test 0) s) D.measure) :
    DifferentiableOn ℂ (realEqualIntegral D W V (test y)) {s : ℂ | σ < s.re} := by
  apply differentiableOn_integral_cexp_mul
    (continuous_quotient_kernel hW hV hWc hVc (test y).continuous).aestronglyMeasurable
    continuous_quotient_logDet.aestronglyMeasurable
  intro t ht
  convert (hInt (t : ℂ) (by simpa using ht)).norm using 1
  funext q
  rw [← integrand_modulate_norm y, realEqualIntegrand_eq]
  dsimp only
  rw [norm_mul, norm_cexp_mul_ofReal, Complex.ofReal_re]

/-- Vanishing for all Schwartz last-row tests in equal rank implies adjacent-rank vanishing
against the restriction of the second coefficient. Both conclusions concern right half-planes
of the ordinary integrals. -/
theorem equalLastRowDescent (D : RealQuotientMeasureData n) (D' : RealQuotientMeasureData (n + 1))
    {a : ℝˣ} {W V : G (n + 1) → ℂ} (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) (hWg : HasGaugeBound W) (hVg : HasGaugeBound V)
    (hvan : ∀ Φ : SchwartzMap Row ℂ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realEqualIntegral D' W V Φ s = 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral (Nat.lt_succ_self n) D W (fun z => V (pad z)) s = 0 := by
  have := sigmaFinite_measure D
  obtain ⟨σ₀, hInt, _⟩ := exists_convergence D' hWc hVc (test 0).continuous
    (invariant_product hW hV) (gauge_on_iwasawa hWg) (gauge_on_iwasawa hVg)
    (hasRapidDecay_schwartz (test 0))
  obtain ⟨σ₁, hCont⟩ := continuousAt_smallerIntegral D hW hV hWc hVc hWg hVg
  refine ⟨max (σ₀ - 1 / 2) σ₁, fun z hz => ?_⟩
  let s := z + (1 / 2 : ℂ)
  have hs₀ : σ₀ < s.re := by
    have he : s.re = z.re + (1 / 2 : ℝ) := by simp [s]
    rw [he]
    linarith [le_max_left (σ₀ - 1 / 2) σ₁]
  have hs₁ : σ₁ < (s - 1 / 2).re := by
    rw [show s - 1 / 2 = z by simp [s]]
    exact (le_max_right _ _).trans_lt hz
  let f := realEqualIntegrand W V (test (0 : Row)) s
  have hf := equal_quotient_integrand_continuous hW hV hWc hVc (test 0) s
  obtain ⟨C, hC, hChart⟩ := lastRowChart_integral D D'
  have hChartInt : Integrable (f ∘ lastRowChart n) (lastRowMeasure n D) :=
    ((hChart f hf.measurable).1).mp (hInt s hs₀)
  let A := D.measure.withDensity (quotientDensity n)
  let H : X → ℂ := fun p => ∫ q, f (lastRowChart n (q, p.1, p.2)) ∂A
  have hHi : Integrable H (volume.prod RealRankZero.unitsHaar) := hChartInt.integral_prod_right
  have hF : ∀ (y : Fin (n + 1) → ℝ) (c : ℝ),
      ∫ p : X, (Real.fourierChar (∑ i, p.1 i * y i + p.2 * c) : ℂ) * H p
        ∂(volume.prod RealRankZero.unitsHaar) = 0 := by
    intro y c
    let v := Fin.snoc (α := fun _ => ℝ) y c
    let fv := realEqualIntegrand W V (test v) s
    have hfvc := equal_quotient_integrand_continuous hW hV hWc hVc (test v) s
    have hfvi : Integrable fv D'.measure := (hInt s hs₀).mono hfvc.aestronglyMeasurable
      (ae_of_all _ fun q => (integrand_modulate_norm v W V s q).le)
    obtain ⟨τ, hτ⟩ := hvan (test v)
    have hzero := eq_zero_on_right (holomorphic_modulate hW hV hWc hVc D' v hInt) hτ s hs₀
    have hFubini := (hChart fv hfvc.measurable).2
    change (∫ q, fv q ∂D'.measure) = 0 at hzero
    rw [hzero] at hFubini
    have hzChart : (∫ q, fv (lastRowChart n q) ∂lastRowMeasure n D) = 0 :=
      (mul_eq_zero.mp hFubini.symm).resolve_left (by exact_mod_cast hC.ne')
    rw [lastRowMeasure, integral_prod_symm (fun q => fv (lastRowChart n q)) ((hChart fv hfvc.measurable).1.mp hfvi)] at hzChart
    rw [← hzChart]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    change _ = ∫ q, fv (lastRowChart n (q, p.1, p.2)) ∂A
    simp only [fv, integrand_modulate v, chart_lastRow]
    rw [integral_const_mul]
    have hphase : phase v (Fin.snoc (α := fun _ => ℝ) p.1 (p.2 : ℝ)) =
        (Real.fourierChar (∑ i, p.1 i * y i + p.2 * c) : ℂ) := by
      unfold phase
      congr 2
      rw [Fin.sum_univ_castSucc]
      simp only [v, Fin.snoc_castSucc, Fin.snoc_last]
    rw [hphase]
  have hHeq : H = fun p => (test 0 (Fin.snoc (α := fun _ => ℝ) p.1 (p.2 : ℝ)) *
      Complex.exp (s * (Real.log |(p.2 : ℝ)| : ℂ))) *
      realUnequalIntegral (Nat.lt_succ_self n) D (fun g => W (g * lastRowFactor p.1 p.2))
        (fun g => V (pad g * lastRowFactor p.1 p.2)) (s - 1 / 2) :=
    funext fun p => fiber_eq D hW hV (test 0) s p
  have hHc : ContinuousAt H (0, 1) := by
    rw [hHeq]
    refine ContinuousAt.mul ?_ ?_
    · exact ((test 0).continuous.comp continuous_row |>.mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          ((Units.continuous_val.comp continuous_snd).abs.log fun p : X =>
            abs_ne_zero.mpr p.2.ne_zero))))).continuousAt
    · exact (hCont _ hs₁).comp_of_eq continuous_lastRowFactor.continuousAt lastRowFactor_zero_one
  have hExtend : ContinuousAt (unitsExtend2 H) (0, 1) := by
    have hOpen : Topology.IsOpenEmbedding (Prod.map (id : (Fin (n + 1) → ℝ) → _)
        (Units.val : ℝˣ → ℝ)) := Topology.IsOpenEmbedding.id.prodMap Units.isOpenEmbedding_val
    have hcomp : unitsExtend2 H ∘ Prod.map id Units.val = H := funext fun p => unitsExtend2_val H p
    have hcc : ContinuousAt (unitsExtend2 H ∘ Prod.map id Units.val) ((0, 1) : X) := by
      rw [hcomp]
      exact hHc
    simpa using (hOpen.continuousAt_iff (g := unitsExtend2 H) (x := ((0, 1) : X))).mp hcc
  have hzero := eq_zero_of_fourier_units_eq_zero hHi hF hExtend
  rw [hHeq] at hzero
  have hb : rowBump n (Fin.snoc (α := fun _ => ℝ) 0 1) = 1 :=
    (rowBump n).one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [rowBump]))
  simpa only [Units.val_one, test_apply, phase_zero, hb, Complex.ofReal_one, abs_one,
    Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one,
    lastRowFactor_zero_one, s, add_sub_cancel_right] using hzero

end Langlands.Global.RankinSelbergGlobal.RealEqualLastRowDescent

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal
open RealUnequalFamily (HasLeftCharacter)
open RealWhittakerTranslatedMellin (HasGaugeBound)

/-- Vanishing of all ordinary real equal-rank integrals of a fixed pair of continuous
Whittaker functions with gauge bounds implies vanishing of the adjacent-rank integral obtained
by restricting the second function. Each vanishing assertion concerns a right half-plane. -/
def RealEqualLastRowDescentStatement : Prop :=
  ∀ (n : ℕ) (D : RealQuotientMeasureData n) (D' : RealQuotientMeasureData (n + 1))
    (a : ℝˣ) (W V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ),
    HasLeftCharacter a W → HasLeftCharacter (-a) V → Continuous W → Continuous V →
    HasGaugeBound W → HasGaugeBound V →
    (∀ Φ : SchwartzMap (Fin (n + 1 + 1) → ℝ) ℂ,
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realEqualIntegral D' W V Φ s = 0) →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realUnequalIntegral (Nat.lt_succ_self n) D W
      (fun g => V (padGL (Nat.le_succ (n + 1)) g)) s = 0

/-- The real equal-rank last-row descent for every pair of compatible quotient measures. -/
theorem realEqualLastRowDescent : RealEqualLastRowDescentStatement :=
  fun _ D D' _ _ _ => RealEqualLastRowDescent.equalLastRowDescent D D'

end Langlands.Global.RankinSelbergGlobal
