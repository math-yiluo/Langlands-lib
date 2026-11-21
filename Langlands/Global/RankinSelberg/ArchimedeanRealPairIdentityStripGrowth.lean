import Langlands.Global.RankinSelberg.ArchimedeanPairIdentityStripGrowth
import Langlands.Global.RankinSelberg.RealUniformPairIdentityReduction

/-! # Real ordinary local normalizations from Jacquet's pair identity -/

noncomputable section

open MeasureTheory
open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairIdentity

open LocalFactor LocalFactor.Archimedean ArchimedeanLocal ArchimedeanInverseMellin
open ArchimedeanRealPairFactor

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

private theorem norm_realEpsilon_eq (ds : List RealBlock) (a : ℝˣ)
    (c : ℝ≥0) (hc : 0 < c) {s t : ℂ} (h : s.re = t.re) :
    ‖(realEpsilon ds a c hc s : ℂ)‖ = ‖(realEpsilon ds a c hc t : ℂ)‖ := by
  simp only [coe_realEpsilon, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr a.ne_zero),
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.one_re, h]

private theorem normalization_of_real_pairIdentity {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : ℂ → X → ℂ) (Kd : ℂ → Y → ℂ) (δ : X → ℝ) (δd : Y → ℝ)
    (σ : ℝ) (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ)
    (hδm : Measurable δ) (hδdm : Measurable δd) (hδ : ∀ x, 0 < δ x) (hδd : ∀ y, 0 < δd y)
    (hK : ∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s)
    (hKd : ∀ s y, Kd s y = Kd 0 y * (δd y : ℂ) ^ s)
    (hKi : ∀ s : ℂ, σ < s.re → Integrable (K s) μ)
    (hKdi : ∀ s : ℂ, σ < s.re → Integrable (Kd s) ν) (hsign : sign ≠ 0)
    (hpair : PairIdentity μ ν (K 0) δ (Kd 0) δd (realPairLFactor ds es).denominator
      (realPairLFactor dds ees).denominator (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign) :
    ∃ R : OrdinaryIntegralNormalization (fun s => ∫ x, K s x ∂μ)
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value := by
  obtain ⟨τ, hτ⟩ := realLFactor_ne_zero (realPairBlocks ds es)
  obtain ⟨τd, hτd⟩ := realLFactor_ne_zero (realPairBlocks dds ees)
  exact pairIdentityNormalizedStripGrowth μ ν K Kd δ δd σ (realPairLFactor ds es)
    (realPairLFactor dds ees) (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign
    hδm hδdm hδ hδd hK hKd hKi hKdi (realLFactor_stripExpType _) (realLFactor_stripExpType _)
    ⟨max τ τd, fun s hs => ⟨hτ s ((le_max_left _ _).trans_lt hs), hτd s ((le_max_right _ _).trans_lt hs)⟩⟩
    (differentiable_realEpsilon _ b c hc) (fun _ => Units.ne_zero _)
    (fun s => norm_realEpsilon_eq _ b c hc (Complex.ofReal_re s.re).symm) hsign hpair

/-- Under the real determinant pair identities and common right convergence, the exact real
ordinary integrals have entire normalizations of exponential strip growth. -/
def RealPairIdentityNormalizedStripGrowthStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (a b : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (V : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (ds es dds ees : List RealBlock) (sign : ℂ) (σ : ℝ), sign ≠ 0 →
    (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W V s) D.measure) →
    (∀ s : ℂ, σ < s.re →
      Integrable (realUnequalDualKernel h W V s) (realUnequalDualMeasure (r := r) a D)) →
    UnequalPairIdentity h a D W V ds es dds ees b sign →
      ∃ R : OrdinaryIntegralNormalization (realUnequalIntegral h D W V)
        (fun s => ((realPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value) ∧
  ∀ (r : ℕ) (a b : ℝˣ) (D : RealQuotientMeasureData r)
    (W V : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ds es dds ees : List RealBlock) (sign : ℂ) (σ : ℝ), sign ≠ 0 →
    (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W V Φ s) D.measure) →
    (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
      (ArchimedeanLocal.dualFunction (r + 1) V) (realFourierTransform b Φ) s) D.measure) →
    EqualPairIdentity a b D W V Φ ds es dds ees sign →
      ∃ R : OrdinaryIntegralNormalization (realEqualIntegral D W V Φ)
        (fun s => ((realPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value

theorem realPairIdentityNormalizedStripGrowth : RealPairIdentityNormalizedStripGrowthStatement := by
  constructor
  · intro r t h a b D W V ds es dds ees sign σ hsign hK hKd hpair
    have := sigmaFinite_measure D
    have := sFinite_dualMeasure (r := r) a D
    exact normalization_of_real_pairIdentity D.measure (realUnequalDualMeasure (r := r) a D)
      (realUnequalIntegrand h W V) (realUnequalDualKernel h W V) quotientDetAbs
      (fun p => quotientDetAbs p.1) σ ds es dds ees b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) sign measurable_quotientDetAbs
      (measurable_quotientDetAbs.comp measurable_fst) quotientDetAbs_pos (fun p => quotientDetAbs_pos p.1)
      (realUnequalIntegrand_eq_mul h W V) (realUnequalDualKernel_eq_mul h W V) hK hKd hsign hpair
  · intro r a b D W V Φ ds es dds ees sign σ hsign hK hKd hpair
    have := sigmaFinite_measure D
    exact normalization_of_real_pairIdentity D.measure D.measure (realEqualIntegrand W V Φ)
      (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) V) (realFourierTransform b Φ))
      quotientDetAbs quotientDetAbs σ ds es dds ees b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) sign
      measurable_quotientDetAbs measurable_quotientDetAbs quotientDetAbs_pos quotientDetAbs_pos
      (realEqualIntegrand_eq_mul W V Φ) (realEqualIntegrand_eq_mul _ _ _) hK hKd hsign hpair

/-- The uniform unequal-rank pair identity supplies ordinary test growth on its coefficient models. -/
theorem realUniformUnequalNormalization_of_pairIdentity
    (hP : RealLocalUniformUnequalPairIdentityStatement) {r t : ℕ} (h : t < r)
    {ds es : List RealBlock} (hds : realRank ds = r + 1) (hes : realRank es = t + 1)
    (a : ℝˣ) (D : RealQuotientMeasureData t)
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {V : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds a) (hV : V ∈ realUniformWhittakerModel t es (-a)) :
    ∃ R : OrdinaryIntegralNormalization (realUnequalIntegral h D W V)
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value := by
  have hWreg := realUniformWhittakerRegularity r ds a W hW
  have hVreg := realUniformWhittakerRegularity t es (-a) V hV
  obtain ⟨σ, hK, hKd, _, _⟩ := realUnequalPairConvergence r t h D a W V
    hWreg.1 hWreg.2 hVreg.1 hVreg.2
  exact realPairIdentityNormalizedStripGrowth.1 r t h a (-a) D W V ds es _ _ _ σ
    (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)) hK hKd
    (hP r t h ds es hds hes a D W V hW hV)

/-- The uniform positive equal-rank pair identity supplies ordinary test growth on its coefficient models. -/
theorem realUniformPositiveEqualNormalization_of_pairIdentity
    (hP : RealLocalUniformPositiveEqualPairIdentityStatement) {r : ℕ} (hr : 0 < r)
    {ds es : List RealBlock} (hds : realRank ds = r + 1) (hes : realRank es = r + 1)
    (a : ℝˣ) (D : RealQuotientMeasureData r)
    {W V : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (hW : W ∈ realUniformWhittakerModel r ds a) (hV : V ∈ realUniformWhittakerModel r es (-a)) :
    ∃ R : OrdinaryIntegralNormalization (realEqualIntegral D W V Φ)
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value := by
  have hWreg := realUniformWhittakerRegularity r ds a W hW
  have hVreg := realUniformWhittakerRegularity r es (-a) V hV
  obtain ⟨σ, hK, hKd, _, _⟩ := realEqualPairConvergence r D a (-a) W V Φ
    hWreg.1 hWreg.2 hVreg.1 hVreg.2
  exact realPairIdentityNormalizedStripGrowth.2 r a (-a) D W V Φ ds es _ _ _ σ
    (pow_ne_zero _ (Units.ne_zero _)) hK hKd (hP r hr ds es hds hes a D W V Φ hW hV)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairIdentity
