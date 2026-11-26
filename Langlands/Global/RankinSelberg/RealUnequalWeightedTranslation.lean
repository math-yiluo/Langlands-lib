import Langlands.Global.RankinSelberg.RealWeightedKernelReflection
import Langlands.Global.RankinSelberg.RealWhittakerTranslatedMellin

/-! # Weighted real unequal reflection for fixed right translates -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalWeightedTranslation

open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal
open ArchimedeanMellinPair (theta)
open ArchimedeanRealPairIdentity (rapidDecay_comp_mul_left rapidDecay_const_mul)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealUnequalFamily (HasLeftCharacter continuous_integrand continuous_dualKernel)
open RealUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs quotientDetAbs_pos
  realUnequalIntegrand_eq_mul realUnequalDualKernel_eq_mul sigmaFinite_quotient)
open RealWeightedKernelReflection (ordinaryWeight reflectedWeight realWeights_data
  realWeightedKernelReflection)
open RealWhittakerTranslatedIntegrals (weightedOrdinary weightedDual realWhittakerTranslatedIntegrals)
open RealWhittakerTranslatedMellin (exists_compact_mellin_bounds hasGaugeBound_of_mem_model)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "R" => fun r t => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ
local notation "Std" => Langlands.Automorphic.realStandardKFinite
local notation "ρ" => ArchimedeanLocal.translateFunction

/-- The Gaussian pair identity for two members of the refined real Whittaker spaces with
normalized growth. -/
theorem weighted_theta_of_growth {r t : ℕ} (h : t < r) (ds es dds ees : List RealBlock)
    (a eb : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ) (D : RealQuotientMeasureData t)
    {W : G (r + 1) → ℂ} {V : G (t + 1) → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds a) (hV : V ∈ realUniformWhittakerModel t es (-a))
    (hN : HasRealPairNormalizedGrowth ds es dds ees eb c hc sign
      (realUnequalIntegral h D W V) (realUnequalDualIntegral h a D W V))
    (rate B : ℝ) (hrate : 0 < rate) {β : ℝ} (hβ : 0 < β) :
    theta D.measure (realUnequalIntegrand h W V 0) quotientDetAbs
      (ordinaryWeight ds es eb c hc sign rate B) β =
      (β : ℂ) * theta (realUnequalDualMeasure (r := r) a D) (realUnequalDualKernel h W V 0)
        (fun p => quotientDetAbs p.1) (reflectedWeight dds ees rate B) β⁻¹ := by
  let μ := D.measure
  let ν := realUnequalDualMeasure (r := r) a D
  let A := realUnequalIntegrand h W V
  let L := realUnequalDualKernel h W V
  let η : Q t × R r t → ℝ := quotientDetAbs ∘ Prod.fst
  let : SigmaFinite μ := sigmaFinite_quotient D
  let : (rectangularMeasure (realSelfDualMeasure a) (r - (t + 1)) (t + 1)).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ν := by
    dsimp only [ν, realUnequalDualMeasure]
    infer_instance
  have hδ : Measurable (quotientDetAbs (t := t)) := continuous_quotientDetAbs.measurable
  have hR := realUniformWhittakerRegularity r ds a W hW
  have hR' := realUniformWhittakerRegularity t es (-a) V hV
  obtain ⟨σ, hσ₁, hσ₂, -, -⟩ := realUnequalPairConvergence r t h D a W V hR.1 hR.2 hR'.1 hR'.2
  have hc' : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → Integrable (A s) μ ∧ Integrable (L s) ν :=
    ⟨σ, fun s hs => ⟨hσ₁ s hs, hσ₂ s hs⟩⟩
  have hn : HasRealPairNormalizedGrowth ds es dds ees eb c hc sign
      (fun s => ∫ x, A s x ∂μ) (fun s => ∫ y, L s y ∂ν) := by
    refine hN.congr (τ := σ) (fun s _ => rfl) (fun s hs => ?_)
    dsimp only [L, ν, realUnequalDualMeasure]
    rw [integral_prod _ (hσ₂ s hs)]
    rfl
  exact realWeightedKernelReflection μ ν A L quotientDetAbs η hδ (hδ.comp measurable_fst)
    quotientDetAbs_pos (fun p => quotientDetAbs_pos p.1) (realUnequalIntegrand_eq_mul h W V)
    (realUnequalDualKernel_eq_mul h W V) hc' ds es dds ees eb c hc sign hn rate B hrate hβ

/-- The scaled Gaussian pair identity extends from the values of two refined real Whittaker
intertwiners to fixed right translates of their values. -/
def RealUnequalWeightedTranslationStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es dds ees : List RealBlock) (a eb : ℝˣ) (c : ℝ≥0) (hc : 0 < c)
    (sign : ℂ) (D : RealQuotientMeasureData t)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)) (B' : Std (t + 1) es →ₗ[ℂ] (G (t + 1) → ℂ)),
      IsRealUniformWhittakerIntertwiner r ds a B → IsRealUniformWhittakerIntertwiner t es (-a) B' →
    (∀ (p : Std (r + 1) ds) (p' : Std (t + 1) es),
      HasRealPairNormalizedGrowth ds es dds ees eb c hc sign
        (realUnequalIntegral h D (B p) (B' p')) (realUnequalDualIntegral h a D (B p) (B' p'))) →
    ∀ (v : Std (r + 1) ds) (v' : Std (t + 1) es) (g : G (r + 1)) (g' : G (t + 1))
      (rate C : ℝ), 0 < rate → ∀ {β : ℝ}, 0 < β →
      let f (x : ℝ) := ordinaryWeight ds es eb c hc sign rate C (β * x)
      let fd (x : ℝ) := (β : ℂ) * reflectedWeight dds ees rate C (β⁻¹ * x)
      let F := weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f
      let Fd := weightedDual h (ρ g (B v)) (ρ g' (B' v')) fd
      Integrable F D.measure ∧ Integrable Fd (realUnequalDualMeasure (r := r) a D) ∧
        (∫ q, F q ∂D.measure) = ∫ p, Fd p ∂realUnequalDualMeasure (r := r) a D

private theorem mem_model {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)} (hB : IsRealUniformWhittakerIntertwiner r ds a B)
    (v : Std (r + 1) ds) : B v ∈ realUniformWhittakerModel r ds a :=
  Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)

set_option maxHeartbeats 1000000 in
theorem realUnequalWeightedTranslation : RealUnequalWeightedTranslationStatement := by
  intro r t h ds es dds ees a eb c hc sign D B B' hB hB' hN v v' g g' rate C hrate β hβ
  let f₀ := ordinaryWeight ds es eb c hc sign rate C
  let fd₀ := reflectedWeight dds ees rate C
  let f (x : ℝ) := f₀ (β * x)
  let fd (x : ℝ) := (β : ℂ) * fd₀ (β⁻¹ * x)
  obtain ⟨hf₀, hfd₀, hrd, hrdd, _, _⟩ := realWeights_data ds es dds ees eb c hc sign hrate C
  have hf : Measurable f := hf₀.comp (measurable_const.mul measurable_id)
  have hfd : Measurable fd := measurable_const.mul (hfd₀.comp (measurable_const.mul measurable_id))
  have hWc : HasLeftCharacter a (B v) := fun u hu x => hB.1.1 v u hu x
  have hVc : HasLeftCharacter (-a) (B' v') := fun u hu x => hB'.1.1 v' u hu x
  obtain ⟨M, Md, hM, hMd, hbound, hboundd⟩ := exists_compact_mellin_bounds h a D hWc hVc
    (hasGaugeBound_of_mem_model (mem_model hB v)) (hasGaugeBound_of_mem_model (mem_model hB' v'))
    g g' f fd (rapidDecay_comp_mul_left hrd hβ)
    (rapidDecay_const_mul (rapidDecay_comp_mul_left hrdd (inv_pos.mpr hβ)) _)
  have hu : HasLeftCharacter a (ρ g (B v)) := by
    intro u hu x
    change B v ((u * x) * g) = _
    rw [mul_assoc, hWc u hu]
    rfl
  have hv : HasLeftCharacter (-a) (ρ g' (B' v')) := by
    intro u hu x
    change B' v' ((u * x) * g') = _
    rw [mul_assoc, hVc u hu]
    rfl
  have huC : Continuous (ρ g (B v)) := (hB.1.2.1 v).continuous.comp (continuous_id.mul_const g)
  have hvC : Continuous (ρ g' (B' v')) := (hB'.1.2.1 v').continuous.comp (continuous_id.mul_const g')
  have hδ := continuous_quotientDetAbs (t := t)
  have hF : AEStronglyMeasurable (weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f) D.measure :=
    ((continuous_integrand h hu hv huC hvC 0).measurable.mul
      (hf.comp hδ.measurable)).aestronglyMeasurable
  have hFd : AEStronglyMeasurable (weightedDual h (ρ g (B v)) (ρ g' (B' v')) fd)
      (realUnequalDualMeasure a D) :=
    ((continuous_dualKernel h hu hv huC hvC 0).measurable.mul
      (hfd.comp (hδ.measurable.comp measurable_fst))).aestronglyMeasurable
  have hBnd (q : Q t) : ‖weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f q‖ ≤ M q := by
    simpa only [OneMemClass.coe_one, one_mul] using hbound q 1 1
  have hBndd (p : Q t × R r t) : ‖weightedDual h (ρ g (B v)) (ρ g' (B' v')) fd p‖ ≤ Md p := by
    simpa only [OneMemClass.coe_one, one_mul] using hboundd p 1 1
  refine ⟨hM.mono' hF (ae_of_all _ hBnd), hMd.mono' hFd (ae_of_all _ hBndd), ?_⟩
  apply realWhittakerTranslatedIntegrals r t h ds es a D f fd hf hfd B B' hB.1 hB'.1 ?_ v v' g g'
    M Md hM hMd hbound hboundd
  intro X Y
  have hEq := weighted_theta_of_growth h ds es dds ees a eb c hc sign D (mem_model hB X)
    (mem_model hB' Y) (hN X Y) rate C hrate hβ
  unfold theta at hEq
  rw [← integral_const_mul] at hEq
  simpa only [weightedOrdinary, weightedDual, f, fd, f₀, fd₀, mul_left_comm] using hEq

end Langlands.Global.RankinSelbergGlobal.RealUnequalWeightedTranslation
