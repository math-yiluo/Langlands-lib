import Langlands.Global.RankinSelberg.ComplexWeightedKernelReflection
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin

/-! # Weighted unequal reflection for fixed right translates -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalWeightedTranslation

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open ArchimedeanLocal
open ArchimedeanMellinPair (theta)
open ArchimedeanRealPairIdentity (rapidDecay_comp_mul_left rapidDecay_const_mul)
open ComplexJacquet (HasComplexPairNormalizedGrowth)
open ComplexUnequalFamily (HasLeftCharacter continuous_ordinaryKernel continuous_dualKernel)
open ComplexUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs quotientDetAbs_pos
  complexUnequalIntegrand_eq_mul complexUnequalDualKernel_eq_mul)
open ComplexWeightedKernelReflection (ordinaryWeight reflectedWeight complexWeights_data complexWeightedKernelReflection)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary weightedDual complexWhittakerTranslatedIntegrals)
open ComplexWhittakerTranslatedMellin (exists_compact_mellin_bounds)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable archimedeanComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "R" => fun r t => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
local notation "Std" => Langlands.Automorphic.complexStandardKFinite
local notation "ρ" => ArchimedeanLocal.translateFunction

private theorem sigmaFinite_quotient {t : ℕ} (D : ComplexQuotientMeasureData t) : SigmaFinite D.measure := by
  let e := leftQuotient_isOpenQuotientMap (U (t + 1))
  let : SecondCountableTopology (G (t + 1)) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (t + 1)).isInducing.secondCountableTopology
  let : LocallyCompactSpace (G (t + 1)) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (t + 1)).locallyCompactSpace
  let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : SigmaCompactSpace (Q t) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr e.surjective]
    exact isSigmaCompact_range e.continuous
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  infer_instance

/-- The Gaussian pair identity on the two finite Whittaker models. -/
theorem weighted_theta_of_growth {r t : ℕ} (h : t < r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a))
    (hN : HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
      (complexUnequalIntegral h D W.val V.val) (complexUnequalDualIntegral h a D W.val V.val))
    (rate B : ℝ) (hrate : 0 < rate) {b : ℝ} (hb : 0 < b) :
    theta D.measure (complexUnequalIntegrand h W.val V.val 0) quotientDetAbs
      (ordinaryWeight ds es a (complexCentralSign es ^ r) rate B) b =
      (b : ℂ) * theta (complexUnequalDualMeasure (r := r) a D) (complexUnequalDualKernel h W.val V.val 0)
        (fun p => quotientDetAbs p.1) (reflectedWeight ds es rate B) b⁻¹ := by
  let μ := D.measure
  let ν := complexUnequalDualMeasure (r := r) a D
  let A := complexUnequalIntegrand h W.val V.val
  let L := complexUnequalDualKernel h W.val V.val
  let η : Q t × R r t → ℝ := quotientDetAbs ∘ Prod.fst
  let : SigmaFinite μ := sigmaFinite_quotient D
  let : (rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ν := by
    dsimp only [ν, complexUnequalDualMeasure]
    infer_instance
  have hδ : Measurable (quotientDetAbs (t := t)) := continuous_quotientDetAbs.measurable
  obtain ⟨σ, hσ⟩ := complexLocalUnequalConvergence h ds es a D W V
  have hc : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → Integrable (A s) μ ∧ Integrable (L s) ν := ⟨σ, hσ⟩
  have hn : HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
      (fun s => ∫ x, A s x ∂μ) (fun s => ∫ y, L s y ∂ν) := by
    obtain ⟨N, Nd, hNa, hNda, hNt, hNdt, ⟨τ, hτ⟩, hFE⟩ := hN
    refine ⟨N, Nd, hNa, hNda, hNt, hNdt, ⟨max σ τ, ?_⟩, hFE⟩
    intro s hs
    obtain ⟨h₁, h₂⟩ := hτ s ((le_max_right _ _).trans_lt hs)
    refine ⟨h₁, ?_⟩
    dsimp only [L, ν, complexUnequalDualMeasure]
    rw [integral_prod _ (hσ s ((le_max_left _ _).trans_lt hs)).2]
    exact h₂
  exact complexWeightedKernelReflection μ ν A L quotientDetAbs η hδ (hδ.comp measurable_fst)
    quotientDetAbs_pos (fun p => quotientDetAbs_pos p.1) (complexUnequalIntegrand_eq_mul h W.val V.val)
    (complexUnequalDualKernel_eq_mul h W.val V.val) hc ds es a _ hn rate B hrate hb

private theorem hasLeftCharacter_translate {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) (g : G (r + 1)) : HasLeftCharacter a (ρ g W.val) := by
  intro u x
  change W.val ((u.val * x) * g) = _
  rw [mul_assoc, complexWhittakerModel_left_equivariant W.2 _ u.2]
  rfl

/-- The scaled Gaussian pair identity extends from finite-model points to fixed right translates of both intertwiners. -/
def ComplexUnequalWeightedTranslationStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData t),
    (∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
      HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
        (complexUnequalIntegral h D W.val V.val) (complexUnequalDualIntegral h a D W.val V.val)) →
    ∀ (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)) (B' : Std (t + 1) es →ₗ[ℂ] (G (t + 1) → ℂ)),
      IsComplexWhittakerIntertwiner r ds a B → IsComplexWhittakerIntertwiner t es (-a) B' →
    ∀ (v : Std (r + 1) ds) (v' : Std (t + 1) es) (g : G (r + 1)) (g' : G (t + 1))
      (rate C : ℝ), 0 < rate → ∀ {b : ℝ}, 0 < b →
      let f (x : ℝ) := ordinaryWeight ds es a (complexCentralSign es ^ r) rate C (b * x)
      let fd (x : ℝ) := (b : ℂ) * reflectedWeight ds es rate C (b⁻¹ * x)
      let F := weightedOrdinary h (ρ g (B v)) (ρ g' (B' v')) f
      let Fd := weightedDual h (ρ g (B v)) (ρ g' (B' v')) fd
      Integrable F D.measure ∧ Integrable Fd (complexUnequalDualMeasure (r := r) a D) ∧
        (∫ q, F q ∂D.measure) = ∫ p, Fd p ∂complexUnequalDualMeasure (r := r) a D

set_option maxHeartbeats 1000000 in
theorem complexUnequalWeightedTranslation : ComplexUnequalWeightedTranslationStatement := by
  intro r t h ds es a D hN B B' hB hB' v v' g g' rate C hrate b hb
  let W : complexWhittakerModel r ds a :=
    ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩
  let V : complexWhittakerModel t es (-a) :=
    ⟨B' v', Submodule.mem_iSup_of_mem B' (Submodule.mem_iSup_of_mem hB' ⟨v', rfl⟩)⟩
  let f₀ := ordinaryWeight ds es a (complexCentralSign es ^ r) rate C
  let fd₀ := reflectedWeight ds es rate C
  let f (x : ℝ) := f₀ (b * x)
  let fd (x : ℝ) := (b : ℂ) * fd₀ (b⁻¹ * x)
  obtain ⟨hf₀, hfd₀, hrd, hrdd, _, _⟩ := complexWeights_data ds es a (complexCentralSign es ^ r) hrate C
  have hf : Measurable f := hf₀.comp (measurable_const.mul measurable_id)
  have hfd : Measurable fd := measurable_const.mul (hfd₀.comp (measurable_const.mul measurable_id))
  obtain ⟨M, Md, hM, hMd, hbound, hboundd⟩ := exists_compact_mellin_bounds h ds es a D W V g g' f fd
    (rapidDecay_comp_mul_left hrd hb) (rapidDecay_const_mul (rapidDecay_comp_mul_left hrdd (inv_pos.mpr hb)) _)
  have hu := hasLeftCharacter_translate W g
  have hv := hasLeftCharacter_translate V g'
  have huC : Continuous (ρ g W.val) := (contMDiff_of_mem_complexWhittakerModel W.2).continuous.comp
    (continuous_id.mul_const g)
  have hvC : Continuous (ρ g' V.val) := (contMDiff_of_mem_complexWhittakerModel V.2).continuous.comp
    (continuous_id.mul_const g')
  have hδ := continuous_quotientDetAbs (t := t)
  have hF : AEStronglyMeasurable (weightedOrdinary h (ρ g W.val) (ρ g' V.val) f) D.measure :=
    ((continuous_ordinaryKernel h hu hv huC hvC 0).measurable.mul (hf.comp hδ.measurable)).aestronglyMeasurable
  have hFd : AEStronglyMeasurable (weightedDual h (ρ g W.val) (ρ g' V.val) fd) (complexUnequalDualMeasure a D) :=
    ((continuous_dualKernel h hu hv huC hvC 0).measurable.mul
    (hfd.comp (hδ.measurable.comp measurable_fst))).aestronglyMeasurable
  have hBnd (q : Q t) : ‖weightedOrdinary h (ρ g W.val) (ρ g' V.val) f q‖ ≤ M q := by
    simpa only [map_one, one_mul] using hbound q 1 1
  have hBndd (p : Q t × R r t) : ‖weightedDual h (ρ g W.val) (ρ g' V.val) fd p‖ ≤ Md p := by
    simpa only [map_one, one_mul] using hboundd p 1 1
  refine ⟨hM.mono' hF (ae_of_all _ hBnd), hMd.mono' hFd (ae_of_all _ hBndd), ?_⟩
  apply complexWhittakerTranslatedIntegrals r t h ds es a D f fd hf hfd ?_ B B' hB hB' v v' g g' M Md hM hMd hbound hboundd
  intro X Y
  have hEq := weighted_theta_of_growth h ds es a D X Y (hN X Y) rate C hrate hb
  unfold theta at hEq
  rw [← integral_const_mul] at hEq
  simpa only [weightedOrdinary, weightedDual, f, fd, f₀, fd₀, mul_left_comm] using hEq

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalWeightedTranslation
