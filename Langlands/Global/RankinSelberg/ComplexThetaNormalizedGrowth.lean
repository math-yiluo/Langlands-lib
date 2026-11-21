import Langlands.Global.RankinSelberg.ArchimedeanThetaNormalizedGrowth
import Langlands.Global.RankinSelberg.ComplexWeightedKernelReflection
import Langlands.Global.RankinSelberg.ComplexUnequalMellinReduction

/-! # The complex normalized pair with growth from its theta reflection -/

noncomputable section

open MeasureTheory Complex
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ComplexThetaNormalizedGrowth

open Langlands.LocalFactor.Archimedean
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal
open ArchimedeanMellinPair (RapidDecay theta archimedeanThetaNormalizedGrowth)
open ArchimedeanRealPairIdentity (norm_kernel kernel_zero_eq)
open ArchimedeanInverseMellin
open ArchimedeanComplexPairFactor (complexLFactor_stripExpType)
open ComplexJacquet (HasComplexPairNormalizedGrowth complexCentralSign_sq)
open ComplexUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs quotientDetAbs_pos
  complexUnequalIntegrand_eq_mul complexUnequalDualKernel_eq_mul)
open ComplexWeightedKernelReflection (pairReflectionFactor differentiable_pairReflectionFactor stripExpType_pairReflectionFactor)

private theorem stripExpType_inv_epsilon (d : ComplexCharacterData) (a : ℂˣ) (c : ℝ≥0) (hc : 0 < c) :
    StripExpType (fun s => (d.epsilon a c hc s : ℂ)⁻¹) := by
  have ha : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  have h := ((StripExpType.ofReal_cpow ha).comp_ofReal_mul (-2)).comp_add (-1)
  refine (((StripExpType.const ((c : ℂ) * (d.character a : ℂ))⁻¹).mul h).mul
    (StripExpType.const (Complex.I ^ d.weight.natAbs)⁻¹)).congr fun s => ?_
  simp only [d.coe_epsilon, mul_inv, ← Complex.cpow_neg, ofReal_neg, ofReal_ofNat, sub_eq_add_neg, ← neg_mul]

private theorem stripExpType_inv_complexEpsilon (ds : List ComplexCharacterData) (a : ℂˣ) (c : ℝ≥0) (hc : 0 < c) :
    StripExpType (fun s => (complexEpsilon ds a c hc s : ℂ)⁻¹) := by
  induction ds with
  | nil => exact (StripExpType.const 1).congr (by simp [complexEpsilon])
  | cons d ds ih =>
    exact ((stripExpType_inv_epsilon d a c hc).mul ih).congr fun s => by
      simp only [complexEpsilon_cons, Units.val_mul, mul_inv]

/-- The inverse complex reflection factor has strip exponential type. -/
theorem stripExpType_pairReflectionFactor_inv (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ) :
    StripExpType (fun s => (pairReflectionFactor ds es a sign s)⁻¹) :=
  ((StripExpType.const sign⁻¹).mul
    (stripExpType_inv_complexEpsilon (complexPairBlocks ds es) a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero))).congr
    fun s => (mul_inv sign (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)).symm

/-- A complex theta reflection gives the normalized growth package for its two determinant transforms. -/
def ComplexThetaNormalizedGrowthStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (Fd : Y → ℂ) (δ : X → ℝ) (δd : Y → ℝ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable Fd ν → Measurable δ → Measurable δd →
    (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    ∀ (σ : ℝ), (∀ x : ℝ, σ ≤ x → Integrable (fun p => ‖F p‖ * δ p ^ x) μ) →
    (∀ x : ℝ, σ ≤ x → Integrable (fun p => ‖Fd p‖ * δd p ^ x) ν) →
    ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ), sign ≠ 0 →
    ∀ (f fd : ℝ → ℂ), Measurable f → Measurable fd → RapidDecay f → RapidDecay fd →
    (∀ s : ℂ, mellin f (-s) = (complexPairLFactor ds es).denominator s *
      pairReflectionFactor ds es a sign s * Complex.exp (s ^ 2)) →
    (∀ s : ℂ, mellin fd (s - 1) = (complexPairLFactor (ds.map ComplexCharacterData.inv)
      (es.map ComplexCharacterData.inv)).denominator (1 - s) * Complex.exp (s ^ 2)) →
    (∀ b : ℝ, 0 < b → theta μ F δ f b = (b : ℂ) * theta ν Fd δd fd b⁻¹) →
    HasComplexPairNormalizedGrowth ds es a sign
      (fun s => ∫ p, F p * (δ p : ℂ) ^ s ∂μ) (fun s => ∫ p, Fd p * (δd p : ℂ) ^ s ∂ν)

theorem complexThetaNormalizedGrowth : ComplexThetaNormalizedGrowthStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F Fd δ δd hF hFd hδm hδdm hδ hδd σ hI hId ds es a sign hsign
    f fd hfm hfdm hf hfd hfmellin hfdmellin hθ
  let L := (complexPairLFactor ds es).denominator
  let Ld := (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
  let E := pairReflectionFactor ds es a sign
  have hE₀ (s : ℂ) : E s ≠ 0 := mul_ne_zero hsign (Units.ne_zero _)
  obtain ⟨N, Nd, hN, hNd, hNt, hNdt, hR, hFE⟩ :=
    archimedeanThetaNormalizedGrowth μ ν F Fd δ δd hF hFd hδm hδdm hδ hδd σ hI hId L Ld E
      (complexLFactor_stripExpType _) (complexLFactor_stripExpType _) (stripExpType_pairReflectionFactor ds es a sign)
      (stripExpType_pairReflectionFactor_inv ds es a sign) (differentiable_pairReflectionFactor ds es a sign) hE₀
      f fd hfm hfdm hf hfd hfmellin hfdmellin hθ
  exact ⟨N, Nd, hN, hNd, hNt.hasStripExponentialGrowth, hNdt.hasStripExponentialGrowth, ⟨σ, fun s hs => hR s hs.le⟩, hFE⟩

/-- Only agreement on a right half-plane is needed to transfer the normalized growth package. -/
theorem normalizedGrowth_congr_right {ds es : List ComplexCharacterData} {a : ℂˣ} {sign : ℂ} {I Id J Jd : ℂ → ℂ}
    (h : HasComplexPairNormalizedGrowth ds es a sign I Id)
    (hR : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → I s = J s ∧ Id s = Jd s) :
    HasComplexPairNormalizedGrowth ds es a sign J Jd := by
  obtain ⟨N, Nd, hN, hNd, hNt, hNdt, ⟨b, hb⟩, hFE⟩ := h
  obtain ⟨σ, hσ⟩ := hR
  refine ⟨N, Nd, hN, hNd, hNt, hNdt, ⟨max σ b, fun s hs => ?_⟩, hFE⟩
  rcases hσ s ((le_max_left _ _).trans_lt hs) with ⟨hl, hr⟩
  simpa only [hl, hr] using hb s ((le_max_right _ _).trans_lt hs)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable archimedeanComplexQBorel

private theorem sigmaFinite_quotient {t : ℕ} (D : ComplexQuotientMeasureData t) : SigmaFinite D.measure := by
  let e := leftQuotient_isOpenQuotientMap (Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ)
  let : SecondCountableTopology (Langlands.GeneralLinear (t + 1) ℂ) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (t + 1)).isInducing.secondCountableTopology
  let : LocallyCompactSpace (Langlands.GeneralLinear (t + 1) ℂ) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (t + 1)).locallyCompactSpace
  let : SigmaCompactSpace (Langlands.GeneralLinear (t + 1) ℂ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : SigmaCompactSpace (LeftUnipotentQuotient t ℂ) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr e.surjective]
    exact isSigmaCompact_range e.continuous
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  infer_instance

private theorem moment_data {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : ℂ → X → ℂ)
    (δ : X → ℝ) (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x)
    (hA : ∀ s x, A s x = A 0 x * (δ x : ℂ) ^ s) (σ : ℝ)
    (hI : ∀ s : ℂ, σ < s.re → Integrable (A s) μ) :
    AEStronglyMeasurable (A 0) μ ∧
      ∀ b : ℝ, σ + 1 ≤ b → Integrable (fun x => ‖A 0 x‖ * δ x ^ b) μ := by
  have hb (b : ℝ) (hb : σ + 1 ≤ b) : σ < (b : ℂ).re := by rw [ofReal_re]; linarith
  refine ⟨?_, fun b h => (hI (b : ℂ) (hb b h)).norm.congr (ae_of_all _ (norm_kernel hδ hA b))⟩
  let b : ℂ := (σ + 1 : ℝ)
  have hM : Measurable (fun x => (δ x : ℂ) ^ (-b)) := (measurable_ofReal.comp hδm).pow_const _
  exact ((hI b (hb (σ + 1) le_rfl)).aestronglyMeasurable.mul hM.aestronglyMeasurable).congr
    (ae_of_all _ fun x => (kernel_zero_eq hδ hA b x).symm)

/-- On the exact unequal-rank quotient kernels a Gaussian theta reflection gives normalized continuation and strip growth. -/
theorem complexUnequalNormalizedGrowth_of_theta {r t : ℕ} (h : t < r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
    (f fd : ℝ → ℂ) (hfm : Measurable f) (hfdm : Measurable fd) (hf : RapidDecay f) (hfd : RapidDecay fd)
    (hMf : ∀ s : ℂ, mellin f (-s) = (complexPairLFactor ds es).denominator s *
      pairReflectionFactor ds es a (complexCentralSign es ^ r) s * Complex.exp (s ^ 2))
    (hMfd : ∀ s : ℂ, mellin fd (s - 1) = (complexPairLFactor (ds.map ComplexCharacterData.inv)
      (es.map ComplexCharacterData.inv)).denominator (1 - s) * Complex.exp (s ^ 2))
    (hθ : ∀ b : ℝ, 0 < b → theta D.measure (complexUnequalIntegrand h W.val V.val 0) quotientDetAbs f b =
      (b : ℂ) * theta (complexUnequalDualMeasure (r := r) a D) (complexUnequalDualKernel h W.val V.val 0)
        (fun p => quotientDetAbs p.1) fd b⁻¹) :
    HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
      (complexUnequalIntegral h D W.val V.val) (complexUnequalDualIntegral h a D W.val V.val) := by
  let μ := D.measure
  let ν := complexUnequalDualMeasure (r := r) a D
  let K := complexUnequalIntegrand h W.val V.val
  let L := complexUnequalDualKernel h W.val V.val
  let δ := quotientDetAbs (t := t)
  let δd : LeftUnipotentQuotient t ℂ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ → ℝ := δ ∘ Prod.fst
  let : SigmaFinite μ := sigmaFinite_quotient D
  let : (rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ν := by dsimp only [ν, complexUnequalDualMeasure]; infer_instance
  have hδm : Measurable δ := continuous_quotientDetAbs.measurable
  have hδdm : Measurable δd := hδm.comp measurable_fst
  have hK := complexUnequalIntegrand_eq_mul h W.val V.val
  have hL := complexUnequalDualKernel_eq_mul h W.val V.val
  obtain ⟨σ, hI⟩ := complexLocalUnequalConvergence h ds es a D W V
  obtain ⟨hKm, hIm⟩ := moment_data μ K δ hδm quotientDetAbs_pos hK σ (fun s hs => (hI s hs).1)
  obtain ⟨hLm, hIdm⟩ := moment_data ν L δd hδdm (fun p => quotientDetAbs_pos p.1) hL σ (fun s hs => (hI s hs).2)
  have hsign : complexCentralSign es ^ r ≠ 0 := pow_ne_zero _ (by
    intro h0
    have hs := complexCentralSign_sq es
    rw [h0, zero_pow (by decide : 2 ≠ 0)] at hs
    exact zero_ne_one hs)
  have hn := complexThetaNormalizedGrowth μ ν (K 0) (L 0) δ δd hKm hLm hδm hδdm quotientDetAbs_pos
    (fun p => quotientDetAbs_pos p.1) (σ + 1) hIm hIdm ds es a _ hsign f fd hfm hfdm hf hfd hMf hMfd hθ
  refine normalizedGrowth_congr_right hn ⟨σ, fun s hs => ⟨?_, ?_⟩⟩
  · exact integral_congr_ae (ae_of_all μ fun p => (hK s p).symm)
  · calc
      _ = ∫ p, L s p ∂ν := integral_congr_ae (ae_of_all ν fun p => (hL s p).symm)
      _ = _ := integral_prod _ (hI s hs).2

end Langlands.Global.RankinSelbergGlobal.ComplexThetaNormalizedGrowth
