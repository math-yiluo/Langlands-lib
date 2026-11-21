import Langlands.Global.RankinSelberg.ArchimedeanPairIdentityStripGrowth
import Langlands.Global.RankinSelberg.ComplexLocalDualConvergence
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Langlands.Automorphic.AssociatedGammaCuspidalEquation

/-! # Complex ordinary local normalizations from Jacquet's pair identity -/

noncomputable section

open MeasureTheory
open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanComplexPairIdentity

open LocalFactor LocalFactor.Archimedean ArchimedeanLocal ArchimedeanInverseMellin
open ArchimedeanRealPairIdentity (PairIdentity ofReal_cpow_eq_exp pairIdentityNormalizedStripGrowth)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

/-- The squared determinant norm at a complex place, on the unipotent quotient. -/
def quotientDetAbs {r : ℕ} (q : LeftUnipotentQuotient r ℂ) : ℝ :=
  complexNormalizedAbs (Matrix.det q.out.val)

private theorem detAbs_pos {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    0 < complexNormalizedAbs (Matrix.det g.val) := by
  unfold complexNormalizedAbs
  exact pow_pos (norm_pos_iff.mpr (GeneralLinear.determinant g).ne_zero) _

private theorem measurable_quotientDetAbs {r : ℕ} : Measurable (quotientDetAbs (r := r)) := by
  have heq : Real.exp ∘ complexQuotientLogDet = quotientDetAbs (r := r) := by
    funext q
    change Real.exp (complexQuotientLogDet q) = quotientDetAbs q
    rw [complexQuotientLogDet_out, Real.exp_log (detAbs_pos q.out)]
    rfl
  rw [← heq]
  exact Real.continuous_exp.measurable.comp
    (continuous_complexQuotientLogDet (r := r)).measurable

private theorem detPower_eq_cpow {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (s : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs g s =
      (complexNormalizedAbs (Matrix.det g.val) : ℂ) ^ s := by
  rw [ofReal_cpow_eq_exp (detAbs_pos g), ArchimedeanLocal.detPower, mul_comm]

private theorem complexEqualIntegrand_eq_mul {r : ℕ}
    (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : (Fin (r + 1) → ℂ) → ℂ)
    (s : ℂ) (q : LeftUnipotentQuotient r ℂ) :
    complexEqualIntegrand W V Φ s q =
      complexEqualIntegrand W V Φ 0 q * (quotientDetAbs q : ℂ) ^ s := by
  simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, detPower_eq_cpow,
    Complex.cpow_zero, mul_one, quotientDetAbs]

private theorem complexUnequalIntegrand_eq_mul {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (s : ℂ) (q : LeftUnipotentQuotient t ℂ) :
    complexUnequalIntegrand h W V s q =
      complexUnequalIntegrand h W V 0 q * (quotientDetAbs q : ℂ) ^ s := by
  have hδ := Complex.ofReal_ne_zero.mpr (detAbs_pos q.out).ne'
  simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    detPower_eq_cpow, quotientDetAbs]
  rw [show s - ((r - t : ℕ) : ℂ) / 2 = (0 - ((r - t : ℕ) : ℂ) / 2) + s by ring,
    Complex.cpow_add _ _ hδ]
  ring

private theorem complexUnequalDualKernel_eq_mul {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (s : ℂ) (p : LeftUnipotentQuotient t ℂ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ) :
    complexUnequalDualKernel h W V s p =
      complexUnequalDualKernel h W V 0 p * (quotientDetAbs p.1 : ℂ) ^ s := by
  have hδ := Complex.ofReal_ne_zero.mpr (detAbs_pos p.1.out).ne'
  simp only [complexUnequalDualKernel, blockKernel, detPower_eq_cpow, quotientDetAbs]
  rw [show s - ((r - t : ℕ) : ℂ) / 2 = (0 - ((r - t : ℕ) : ℂ) / 2) + s by ring,
    Complex.cpow_add _ _ hδ]
  ring

private theorem sigmaFinite_measure {r : ℕ} (D : ComplexQuotientMeasureData r) :
    SigmaFinite D.measure := by
  have : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℂ))
  have : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (Langlands.GeneralLinear (r + 1) ℂ) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℂ))
  have : SigmaCompactSpace (LeftUnipotentQuotient r ℂ) := by
    have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) ℂ)
    exact isSigmaCompact_univ_iff.mp (Set.range_eq_univ.mpr hq.surjective ▸
      isSigmaCompact_range hq.continuous)
  have := D.unipotentHaar_rightInvariant
  have := D.compatible.regular
  infer_instance

private theorem sFinite_dualMeasure {r t : ℕ} (a : ℂˣ) (D : ComplexQuotientMeasureData t) :
    SFinite (complexUnequalDualMeasure (r := r) a D) := by
  have := sigmaFinite_measure D
  have := (complexSelfDualMeasure a).isAddHaar
  let ν := (complexSelfDualMeasure a).measure
  have : SigmaFinite ν := inferInstance
  have : SigmaFinite (rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)) := by
    let : ∀ _ : Fin (r - (t + 1)), SigmaFinite (Measure.pi (fun _ : Fin (t + 1) => ν)) :=
      fun _ => Measure.pi.sigmaFinite _
    exact Measure.pi.sigmaFinite _
  unfold complexUnequalDualMeasure
  infer_instance

private theorem denominator_stripExpType (ds es : List ComplexCharacterData) :
    StripExpType (complexPairLFactor ds es).denominator := by
  refine (StripExpType.list_prod (complexPairBlocks ds es) (fun d => d.lFactor.denominator)
    (fun d _ => ?_)).congr fun s => (denominator_complexLFactor _ s).symm
  exact inv_Gammaℂ_stripExpType.comp_add (d.exponent + (d.weight.natAbs : ℂ) / 2)

private theorem norm_complexEpsilon_eq (ds : List ComplexCharacterData) (a : ℂˣ)
    (c : ℝ≥0) (hc : 0 < c) {s t : ℂ} (h : s.re = t.re) :
    ‖(complexEpsilon ds a c hc s : ℂ)‖ = ‖(complexEpsilon ds a c hc t : ℂ)‖ := by
  simp only [coe_complexEpsilon, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr a.ne_zero),
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.sub_re, Complex.one_re, h]

private theorem normalization_of_pairIdentity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : ℂ → X → ℂ) (Kd : ℂ → Y → ℂ) (δ : X → ℝ) (δd : Y → ℝ)
    (σ : ℝ) (ds es dds ees : List ComplexCharacterData) (b : ℂˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ)
    (hδm : Measurable δ) (hδdm : Measurable δd) (hδ : ∀ x, 0 < δ x) (hδd : ∀ y, 0 < δd y)
    (hK : ∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s)
    (hKd : ∀ s y, Kd s y = Kd 0 y * (δd y : ℂ) ^ s)
    (hKi : ∀ s : ℂ, σ < s.re → Integrable (K s) μ)
    (hKdi : ∀ s : ℂ, σ < s.re → Integrable (Kd s) ν) (hsign : sign ≠ 0)
    (hpair : PairIdentity μ ν (K 0) δ (Kd 0) δd (complexPairLFactor ds es).denominator
      (complexPairLFactor dds ees).denominator (fun s => (complexPairEpsilon ds es b c hc s : ℂ)) sign) :
    ∃ R : OrdinaryIntegralNormalization (fun s => ∫ x, K s x ∂μ)
      (fun s => ((complexPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value := by
  obtain ⟨τ, hτ⟩ := complexPairLFactor_denominator_ne_zero ds es
  obtain ⟨τd, hτd⟩ := complexPairLFactor_denominator_ne_zero dds ees
  exact pairIdentityNormalizedStripGrowth μ ν K Kd δ δd σ (complexPairLFactor ds es)
    (complexPairLFactor dds ees) (fun s => (complexPairEpsilon ds es b c hc s : ℂ)) sign
    hδm hδdm hδ hδd hK hKd hKi hKdi (denominator_stripExpType ds es)
    (denominator_stripExpType dds ees)
    ⟨max τ τd, fun s hs => ⟨hτ s ((le_max_left _ _).trans_lt hs), hτd s ((le_max_right _ _).trans_lt hs)⟩⟩
    (differentiable_complexEpsilon _ b c hc) (fun _ => Units.ne_zero _)
    (fun s => norm_complexEpsilon_eq _ b c hc (Complex.ofReal_re s.re).symm) hsign hpair

/-- The unequal-rank pair identity on the actual complex quotient and rectangular measures. -/
def UnequalPairIdentity {r t : ℕ} (h : t < r) (a b : ℂˣ) (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (ds es dds ees : List ComplexCharacterData) (sign : ℂ) : Prop :=
  PairIdentity D.measure (complexUnequalDualMeasure (r := r) a D)
    (complexUnequalIntegrand h W V 0) quotientDetAbs
    (complexUnequalDualKernel h W V 0) (fun p => quotientDetAbs p.1)
    (complexPairLFactor ds es).denominator (complexPairLFactor dds ees).denominator
    (fun s => (complexPairEpsilon ds es b ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)) sign

/-- The equal-rank pair identity on the actual complex quotient measure, with Fourier parameter `a`. -/
def EqualPairIdentity {r : ℕ} (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ds es dds ees : List ComplexCharacterData) (sign : ℂ) : Prop :=
  PairIdentity D.measure D.measure (complexEqualIntegrand W V Φ 0) quotientDetAbs
    (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
      (ArchimedeanLocal.dualFunction (r + 1) V)
      (complexFourierTransform a Φ) 0) quotientDetAbs
    (complexPairLFactor ds es).denominator (complexPairLFactor dds ees).denominator
    (fun s => (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)) sign

/-- The exact complex ordinary integrals have entire normalizations of exponential strip
growth when their determinant pair identities hold. The equal-rank clause assumes joint
absolute convergence on a right half-plane. -/
def ComplexPairIdentityNormalizedStripGrowthStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (a b : ℂˣ) (D : ComplexQuotientMeasureData t)
    (ds es dds ees : List ComplexCharacterData) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a)) (sign : ℂ), sign ≠ 0 →
    UnequalPairIdentity h a b D W V ds es dds ees sign →
      ∃ R : OrdinaryIntegralNormalization (complexUnequalIntegral h D W V)
        (fun s => ((complexPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value) ∧
  ∀ (r : ℕ) (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ds es dds ees : List ComplexCharacterData) (sign : ℂ) (σ : ℝ), sign ≠ 0 →
    (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W V Φ s) D.measure) →
    (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
      (ArchimedeanLocal.dualFunction (r + 1) V) (complexFourierTransform a Φ) s) D.measure) →
    EqualPairIdentity a D W V Φ ds es dds ees sign →
      ∃ R : OrdinaryIntegralNormalization (complexEqualIntegral D W V Φ)
        (fun s => ((complexPairLFactor ds es).denominator s)⁻¹), HasStripExponentialGrowth R.value

theorem complexPairIdentityNormalizedStripGrowth : ComplexPairIdentityNormalizedStripGrowthStatement := by
  constructor
  · intro r t h a b D ds es dds ees W V sign hsign hpair
    have := sigmaFinite_measure D
    have := sFinite_dualMeasure (r := r) a D
    obtain ⟨σ, hσ⟩ := complexLocalUnequalConvergence h ds es a D W V
    exact normalization_of_pairIdentity D.measure (complexUnequalDualMeasure (r := r) a D)
      (complexUnequalIntegrand h W V) (complexUnequalDualKernel h W V)
      quotientDetAbs (fun p => quotientDetAbs p.1) σ ds es dds ees b ‖(a : ℂ)‖₊
      (nnnorm_pos.mpr a.ne_zero) sign measurable_quotientDetAbs
      (measurable_quotientDetAbs.comp measurable_fst) (fun q => detAbs_pos q.out)
      (fun p => detAbs_pos p.1.out) (complexUnequalIntegrand_eq_mul h W V)
      (complexUnequalDualKernel_eq_mul h W V) (fun s hs => (hσ s hs).1) (fun s hs => (hσ s hs).2)
      hsign hpair
  · intro r a D W V Φ ds es dds ees sign σ hsign hK hKd hpair
    have := sigmaFinite_measure D
    exact normalization_of_pairIdentity D.measure D.measure (complexEqualIntegrand W V Φ)
      (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) V)
        (complexFourierTransform a Φ)) quotientDetAbs quotientDetAbs σ ds es dds ees a ‖(a : ℂ)‖₊
      (nnnorm_pos.mpr a.ne_zero) sign measurable_quotientDetAbs measurable_quotientDetAbs
      (fun q => detAbs_pos q.out) (fun q => detAbs_pos q.out) (complexEqualIntegrand_eq_mul W V Φ)
      (complexEqualIntegrand_eq_mul _ _ _) hK hKd hsign hpair

end Langlands.Global.RankinSelbergGlobal.ArchimedeanComplexPairIdentity
