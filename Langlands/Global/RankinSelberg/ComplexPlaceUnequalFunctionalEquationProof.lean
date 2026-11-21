import Langlands.Global.RankinSelberg.ComplexGapDualMellin
import Langlands.Global.RankinSelberg.ComplexGapGrowthFromSeparatedTheta
import Langlands.Global.RankinSelberg.ComplexGapOrdinaryMellin
import Langlands.Global.RankinSelberg.ComplexGapScaleComparison
import Langlands.Global.RankinSelberg.ComplexUnequalFromMonomialGrowth
import Langlands.HarmonicAnalysis.Distribution.RenardHeckeCompactHaar

/-! # The local complex unequal-rank functional equation -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean (unitaryCompact)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.Automorphic (complexStandardKFinite)
open Langlands.GeneralLinear (determinant weylLong)
open Langlands.GodementJacquet (complexNormalizedAbs_det_pos)
open Langlands.HarmonicAnalysis.Distribution.RenardHecke
  (isInvInvariant_of_compact isProbabilityMeasure_haarMeasure_top)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure complexUnequalIntegral complexUnequalDualIntegral)
open ArchimedeanMellinPair (separatedTheta)
open ArchimedeanRealPairIdentity (rapidDecay_comp_mul_left)
open ComplexGapCanonicalGrowth (ComplexGapMonomialGrowth)
open ComplexGapDualChart (retainedTail)
open ComplexGapDualHaar (dualChartMeasure sigmaFinite_dualChartMeasure complexGapDualHaar)
open ComplexGapDualSeparation (complexGapDualMellin complexGapDualSeparation dualSeparatedKernel
  dualSeparatedKernel_mul_profiles dualLeadingDet measurable_dualLeadingDet dualLeadingDet_pos dualProductDet)
open ComplexGapExactRestriction (complexGapExactRestriction rotatedValue)
open ComplexGapGaussianFactors (gaussianFactors gaussianPolynomial_eval_factors)
open ComplexGapMellinWeights (adjoiningPhase complexGapGrowthFromSeparatedTheta)
open ComplexGapOrdinarySeparation (complexGapOrdinaryMellin ordinarySeparatedKernel ordinarySeparatedKernel_mul_profiles
  ordinaryProductDet ordinaryWeylPhase ordinaryChartMeasure sigmaFinite_ordinaryChartMeasure integrable_ordinarySeparatedKernel)
open ComplexGapRankCoordinates (rankLT)
open ComplexGapScaleComparison (complexGapScaleComparison)
open ComplexGapSeparatedKernels (adjoiningWeylSigns)
open ComplexGapSquareReflection (leadingSquareTest leadingSquareTest_finite)
open ComplexGapTriangularChart (Outer)
open ComplexGodementGaussianPolynomial (gaussianPolynomial)
open ComplexJacquet (HasComplexPairNormalizedGrowth)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)
open ComplexUnequalFamily (HasLeftCharacter)
open ComplexUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs sigmaFinite_quotient)
open ComplexWeightedKernelReflection (ordinaryWeight reflectedWeight complexWeights_data)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "SD" => complexSelfDualMeasure

private theorem whittakerValue_from_intertwiner (r : ℕ) (ds : List ComplexCharacterData)
    (hds : ds.length = r + 1) (a : ℂˣ) (W : complexWhittakerModel r ds (-a)) :
    ∃ (A : complexStandardKFinite (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)),
      IsComplexWhittakerIntertwiner r ds (-a) A ∧ ∃ u, A u = W.val := by
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hds
  let A := continuedJacquet (SD a) a l p
  have hW : W.val ∈ LinearMap.range A :=
    le_of_eq (complexJacquetMultiplicityOne r (SD a) a l p).2 W.2
  exact ⟨A, complexJacquetIntertwiner r (SD a) a l p, hW⟩

section Gap

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "LowerIndex" => t + 1 + q
local notation "Rank" => t + 1 + q + 1
local notation "TailSize" => q + 1
local notation "Ord" => Q t × (Outer Small q × Unip TailSize)
local notation "Dual" => Q t × (Outer Small q × (M q Small × Unip TailSize))

private theorem adjoining_mul_ordinaryWeylPhase (d : ComplexCharacterData) (es : List ComplexCharacterData)
    (hes : es.length = Small) : adjoiningPhase d es * ordinaryWeylPhase t q d =
      (d.inv.character (determinant (weylLong TailSize ℂ)) : ℂ) := by
  let S := (d.inv.character (determinant (weylLong TailSize ℂ)) : ℂ)
  have h := adjoiningWeylSigns t q d
  change S * (d.character ((-1 : ℂˣ) ^ Small) : ℂ) = ordinaryWeylPhase t q d at h
  have he : S * adjoiningPhase d es = ordinaryWeylPhase t q d := by
    simpa only [adjoiningPhase, hes] using h
  have hp : adjoiningPhase d es * adjoiningPhase d es = 1 := by
    have hp' : ((-1 : ℂˣ) ^ es.length) * ((-1 : ℂˣ) ^ es.length) = 1 := by
      rw [← mul_pow]
      simp
    rw [adjoiningPhase, ← Units.val_mul, ← map_mul, hp', map_one, Units.val_one]
  calc
    _ = adjoiningPhase d es * (S * adjoiningPhase d es) := by rw [he]
    _ = S * (adjoiningPhase d es * adjoiningPhase d es) := by ring
    _ = S := by rw [hp, mul_one]

set_option maxHeartbeats 2200000 in
private theorem complexGapMonomialGrowth_from_lower
    (hLower : ComplexGapCanonicalGrowth.ComplexLocalUnequalGrowthAtRanks LowerIndex t (rankLT t q)) :
    ComplexGapMonomialGrowth t q := by
  intro ds es hds hes a D d U i cTest B hB f W _hW
  let Φ := operatorToEntry (gaussianPolynomial (MvPolynomial.monomial i cTest))
  let T := gaussianFactors Small q i cTest
  have hΦ : ∀ x, Φ x = T.eval Small q x := gaussianPolynomial_eval_factors Small q i cTest
  let V : complexWhittakerModel t es a :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  obtain ⟨A, hA, u, hu⟩ := whittakerValue_from_intertwiner LowerIndex ds hds a U
  let : CompactSpace (KU Rank) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let κ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (KU Rank))
  let hκ : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let : κ.IsHaarMeasure := hκ
  let : IsProbabilityMeasure κ := isProbabilityMeasure_haarMeasure_top
  have hκinv : κ.IsInvInvariant := isInvInvariant_of_compact κ
  obtain ⟨cH, _, hExact⟩ := complexGapExactRestriction t q a κ hκ hκinv
  obtain ⟨hFo, σo, hOrd⟩ := complexGapOrdinaryMellin t q D a κ hκ cH d T Φ ds es U V
    (fun g => (hExact ds hds d Φ T hΦ U g 0).1.2)
  obtain ⟨hFd, σd, hDual⟩ := complexGapDualMellin t q D a κ hκ hκinv cH d T Φ hΦ ds es hds hes U V W
    (fun g x => ((hExact ds hds d Φ T hΦ U g 0).2 x).2)
  let μo := D.measure.prod (ordinaryChartMeasure t q a κ)
  let μd := D.measure.prod (dualChartMeasure t q a κ)
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : SigmaFinite (ordinaryChartMeasure t q a κ) := sigmaFinite_ordinaryChartMeasure t q a κ
  let : SigmaFinite (dualChartMeasure t q a κ) := sigmaFinite_dualChartMeasure t q a κ
  let σ := max σo σd
  let δo (p : Ord) := quotientDetAbs p.1
  let ηo (p : Ord) := δ p.2.1.1.1.1
  let δd (p : Dual) := quotientDetAbs p.1
  let ηd := dualLeadingDet t q
  let Co := ordinaryWeylPhase t q d * (cH : ℂ)
  let F₀ := ordinarySeparatedKernel t q false a d T U.val V.val (fun _ => 1) (fun _ => 1)
  let Fd₀ := dualSeparatedKernel t q a d T U.val V.val (fun _ => 1) (fun _ => 1)
  let Fo (p : Ord) := Co * F₀ p
  let Fd (p : Dual) := (cH : ℂ) * Fd₀ p
  have hηo : Measurable ηo := by
    have hLead : Continuous (fun p : Ord => p.2.1.1.1.1) := by fun_prop
    exact ((Units.continuous_val.comp hLead).matrix_det.norm.pow 2).measurable
  have hMo (z : ℝ) (hz : σ ≤ z) : Integrable (fun p => ‖Fo p‖ * (δo p * ηo p) ^ z) μo := by
    have h := (hOrd (z : ℂ) (by simpa using (le_max_left σo σd).trans hz)).1.const_mul ‖Co‖
    simpa only [Fo, norm_mul, mul_assoc, Complex.ofReal_re, ordinaryProductDet, δo, ηo] using h
  have hMd (z : ℝ) (hz : σ ≤ z) : Integrable (fun p => ‖Fd p‖ * (δd p * ηd p) ^ z) μd := by
    have h := (hDual (z : ℂ) (by simpa using (le_max_right σo σd).trans hz)).1.const_mul ‖(cH : ℂ)‖
    simpa only [Fd, norm_mul, mul_assoc, Complex.ofReal_re, dualProductDet, δd, ηd] using h
  refine complexGapGrowthFromSeparatedTheta μo μd Fo Fd δo ηo δd ηd
    (hFo.const_mul Co) (hFd.const_mul (cH : ℂ)) (continuous_quotientDetAbs.measurable.comp measurable_fst)
    hηo (continuous_quotientDetAbs.measurable.comp measurable_fst) (measurable_dualLeadingDet t q)
    (fun p => quotientDetAbs_pos p.1) (fun _ => complexNormalizedAbs_det_pos _)
    (fun p => quotientDetAbs_pos p.1) (dualLeadingDet_pos t q) σ hMo hMd LowerIndex d ds es a ?_ _ _ ?_
  · intro b c hb hc
    let w₁ := ordinaryWeight ds es (-a) (complexCentralSign es ^ LowerIndex) (1 / 2) 0
    let w₂ := ordinaryWeight [d] es a 1 (1 / 2) 0
    let wd₁ := reflectedWeight ds es (1 / 2) 0
    let wd₂ := reflectedWeight [d] es (1 / 2) 0
    let f₁ (x : ℝ) := w₁ (b * x)
    let f₂ (x : ℝ) := w₂ (c * x)
    let k₁ (x : ℝ) := wd₁ (b⁻¹ * x)
    let k₂ (x : ℝ) := wd₂ (c⁻¹ * x)
    let F := ordinarySeparatedKernel t q false a d T U.val V.val f₁ f₂
    let Fm := ordinarySeparatedKernel t q true a d T U.val V.val f₁ k₂
    let F' := dualSeparatedKernel t q a d T U.val V.val k₁ k₂
    obtain ⟨hw₁m, hwd₁m, hw₁, hwd₁, _, _⟩ :=
      complexWeights_data ds es (-a) (complexCentralSign es ^ LowerIndex) (rate := 1 / 2) (by norm_num) 0
    obtain ⟨hw₂m, hwd₂m, hw₂, hwd₂, _, _⟩ :=
      complexWeights_data [d] es a 1 (rate := 1 / 2) (by norm_num) 0
    have hf₁m : Measurable f₁ := hw₁m.comp (measurable_const.mul measurable_id)
    have hf₂m : Measurable f₂ := hw₂m.comp (measurable_const.mul measurable_id)
    have hk₁m : Measurable k₁ := hwd₁m.comp (measurable_const.mul measurable_id)
    have hk₂m : Measurable k₂ := hwd₂m.comp (measurable_const.mul measurable_id)
    have hf₁ := rapidDecay_comp_mul_left hw₁ hb
    have hf₂ := rapidDecay_comp_mul_left hw₂ hc
    have hk₁ := rapidDecay_comp_mul_left hwd₁ (inv_pos.mpr hb)
    have hk₂ := rapidDecay_comp_mul_left hwd₂ (inv_pos.mpr hc)
    have hF : Integrable F μo :=
      integrable_ordinarySeparatedKernel t q D a κ hκ false d T ds es U V f₁ f₂ hf₁m hf₂m hf₁ hf₂
    have hFm : Integrable Fm μo :=
      integrable_ordinarySeparatedKernel t q D a κ hκ true d T ds es U V f₁ k₂ hf₁m hk₂m hf₁ hk₂
    let Ud : complexWhittakerModel LowerIndex (dualData ds) a :=
      ⟨ArchimedeanLocal.dualFunction Rank U.val, by simpa only [neg_neg] using dualFunction_mem hds U.2⟩
    let Vd : complexWhittakerModel t (dualData es) (-a) :=
      ⟨ArchimedeanLocal.dualFunction Small V.val, dualFunction_mem hes V.2⟩
    have hUcov : HasLeftCharacter (-a) U.val := fun u₀ g => complexWhittakerModel_left_equivariant U.2 u₀.val u₀.2 g
    have hVcov : HasLeftCharacter a V.val := fun u₀ g => complexWhittakerModel_left_equivariant V.2 u₀.val u₀.2 g
    have hRaw := complexGapDualHaar t q D a κ hκ hκinv _ _ Ud Vd d Φ T hΦ 0 k₁ k₂ hk₁m hk₂m hk₁ hk₂
    have hF' : Integrable F' μd :=
      (complexGapDualSeparation t q D a κ hκ d Φ T hΦ U.val V.val hUcov hVcov k₁ k₂ hRaw).1
    have hN (U₀ : complexWhittakerModel LowerIndex ds (-a)) (V₀ : complexWhittakerModel t es a) :=
      hLower ds es hds hes a D U₀.val V₀.val U₀.2 V₀.2
    have hT (p : Outer Small q) (Z : Unip TailSize) : FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun v : KU Small => fun X : M Small Small =>
          leadingSquareTest t q (retainedTail Small q p Z) T.leading (v.val⁻¹.val * X))) :=
      leadingSquareTest_finite t q p Z _
    let S := (d.inv.character (determinant (weylLong TailSize ℂ)) : ℂ)
    have hScale : S * (∫ p, F p ∂μo) = ((b * c : ℝ) : ℂ) * ∫ p, F' p ∂μd := by
      have hEq := complexGapScaleComparison t q D a κ hκ d ds es hes T hT hN A hA B hB u f b c hb hc
        (1 / 2) 0 (by norm_num)
      simpa only [hu] using hEq (hu.symm ▸ hF) (hu.symm ▸ hFm) (hu.symm ▸ hF')
    have ho (p : Ord) : Fo p * (w₁ (b * δo p) * w₂ (c * ηo p)) = Co * F p := by
      unfold F Fo
      rw [ordinarySeparatedKernel_mul_profiles]
      change Co * F₀ p * (f₁ (δo p) * f₂ (ηo p)) = Co * (F₀ p * (f₁ (δo p) * f₂ (ηo p)))
      exact mul_assoc _ _ _
    have hd (p : Dual) : Fd p * (wd₁ (b⁻¹ * δd p) * wd₂ (c⁻¹ * ηd p)) = (cH : ℂ) * F' p := by
      unfold F' Fd
      rw [dualSeparatedKernel_mul_profiles]
      ring
    change adjoiningPhase d es * separatedTheta μo Fo δo ηo w₁ w₂ b c =
      ((b * c : ℝ) : ℂ) * separatedTheta μd Fd δd ηd wd₁ wd₂ b⁻¹ c⁻¹
    unfold separatedTheta
    simp_rw [ho, hd, integral_const_mul]
    have hPhase : adjoiningPhase d es * ordinaryWeylPhase t q d = S := adjoining_mul_ordinaryWeylPhase t q d es hes
    calc
      _ = (cH : ℂ) * (S * ∫ p, F p ∂μo) := by unfold Co; rw [← hPhase]; ring
      _ = _ := by rw [hScale]; ring
  · refine ⟨σ, fun s hs => ⟨?_, ?_⟩⟩
    · have h := (hOrd s ((le_max_left σo σd).trans hs.le)).2
      change (∫ p, (Co * F₀ p) * (ordinaryProductDet t q p : ℂ) ^ s ∂μo) = _
      simp_rw [mul_assoc Co, integral_const_mul]
      exact h.symm
    · have h := (hDual s ((le_max_right σo σd).trans hs.le)).2
      change (∫ p, ((cH : ℂ) * Fd₀ p) * (dualProductDet t q p : ℂ) ^ s ∂μd) = _
      simp_rw [mul_assoc (cH : ℂ), integral_const_mul]
      exact h.symm

end Gap

/-- The local Jacquet functional equation for complex induced representations of unequal ranks. -/
theorem complexLocalUnequalFunctionalEquation : ComplexLocalUnequalFunctionalEquationStatement :=
  complexUnequalFromMonomialGrowth complexGapMonomialGrowth_from_lower

end Langlands.Global.RankinSelbergGlobal
