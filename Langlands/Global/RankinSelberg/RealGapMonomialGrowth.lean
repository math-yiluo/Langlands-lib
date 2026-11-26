import Langlands.Global.RankinSelberg.RealGapDualMellin
import Langlands.Global.RankinSelberg.RealGapOrdinaryMellin
import Langlands.Global.RankinSelberg.RealGapScaleComparison
import Langlands.Global.RankinSelberg.RealGapGaussianFactors
import Langlands.Global.RankinSelberg.RealGapGrowthFromSeparatedTheta
import Langlands.Global.RankinSelberg.RealUniformWhittakerDual
import Langlands.Global.RankinSelberg.RealLocalCharacterGrowthInterfaces
import Langlands.Global.RankinSelberg.RealAdjacentNormalizedProducts
import Langlands.Global.RankinSelberg.RealMatrixCoefficientGrowth
import Langlands.HarmonicAnalysis.Distribution.RenardHeckeCompactHaar
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # The real larger-gap equation for rotated split Gaussian monomial values -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapMonomialGrowth

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant weylLong)
open Langlands.HarmonicAnalysis.Distribution.RenardHecke
  (isInvInvariant_of_compact isProbabilityMeasure_haarMeasure_top)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs realSelfDualMeasure realUnequalIntegral
  realUnequalDualIntegral)
open ArchimedeanMellinPair (separatedTheta)
open ArchimedeanRealPairIdentity (rapidDecay_comp_mul_left)
open RealJacquet (detCharacter realAdjacentWeylSign HasRealPairNormalizedGrowth
  RealLocalUnequalCharacterGrowthAtRanks)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapDualHaar (dualChartMeasure sigmaFinite_dualChartMeasure realGapDualHaar)
open RealGapDualSeparation (realGapDualMellin realGapDualSeparation dualSeparatedKernel
  dualSeparatedKernel_mul_profiles dualLeadingDet measurable_dualLeadingDet dualLeadingDet_pos dualProductDet)
open RealGapExactRestriction (realGapExactRestriction rotatedValue)
open RealGapGaussianFactors (gaussianFactors gaussianPolynomial_eval_factors)
open RealGapMellinWeights (realGapGrowthFromSeparatedTheta)
open RealGapOrdinarySeparation (realGapOrdinaryMellin ordinarySeparatedKernel ordinarySeparatedKernel_mul_profiles
  ordinaryProductDet ordinaryChartMeasure sigmaFinite_ordinaryChartMeasure integrable_ordinarySeparatedKernel)
open RealGapRankCoordinates (rankLT)
open RealGapScaleComparison (realGapScaleComparison)
open RealGapTriangularChart (Outer)
open RealGapDualChart (retainedTail)
open RealGapLeadingFourier (leadingRestriction)
open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial)
open RealUnequalFamily (HasLeftCharacter)
open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs sigmaFinite_quotient)
open RealUniformWhittakerDual (dualCharacterBlocks realUniformWhittakerCharacterDual)
open RealWeightedKernelReflection (ordinaryWeight reflectedWeight realWeights_data pairReflectionFactor)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℝ
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "Std" => Langlands.Automorphic.realStandardKFinite

local instance gapMonomialGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapMonomialGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapMonomialGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapMonomialGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapMonomialUMeasurable (n : ℕ) : MeasurableSpace (Unip n) := borel _
local instance gapMonomialUBorel (n : ℕ) : BorelSpace (Unip n) := ⟨rfl⟩
local instance gapMonomialQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapMonomialQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

private theorem mem_model {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)} (hB : IsRealUniformWhittakerIntertwiner r ds a B)
    (v : Std (r + 1) ds) : B v ∈ realUniformWhittakerModel r ds a :=
  Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)

/-- A real character does not distinguish an element of order two from its inverse. -/
private theorem inverse_character_of_sq (c : RealCharacterData) (x : ℝˣ) (hx : x * x = 1) :
    (c.inverse.character x : ℂ) = (c.character x : ℂ) := by
  have h1 : c.character x * c.character x = 1 := by rw [← map_mul, hx, map_one]
  rw [RealCharacterData.inverse_character]
  change (((c.character x)⁻¹ : ℂˣ) : ℂ) = _
  rw [inv_eq_of_mul_eq_one_right h1]

private theorem determinant_weylLong_sq (m : ℕ) :
    determinant (weylLong m ℝ) * determinant (weylLong m ℝ) = 1 := by
  rw [← map_mul, Langlands.GeneralLinear.weylLong_mul_self, map_one]

/-- The Weyl factor of the adjoining rank is the same for a real character and its inverse. -/
private theorem weylSign_inverse (r : ℕ) (c : RealCharacterData) :
    realAdjacentWeylSign r c.inverse = realAdjacentWeylSign r c := by
  unfold realAdjacentWeylSign detCharacter
  change (c.inverse.character (determinant (weylLong (r + 2) ℝ)) : ℂ) *
      (c.inverse.character (determinant (weylLong (r + 1) ℝ)) : ℂ) =
    (c.character (determinant (weylLong (r + 2) ℝ)) : ℂ) *
      (c.character (determinant (weylLong (r + 1) ℝ)) : ℂ)
  rw [inverse_character_of_sq c _ (determinant_weylLong_sq _),
    inverse_character_of_sq c _ (determinant_weylLong_sq _)]

/-- The Weyl and central constants of the ordinary and dual restrictions differ by the
adjoining phase and the tail Weyl scalar of the scale comparison. -/
private theorem phase_identity (t q : ℕ) (c : RealCharacterData) (C : ℂ) :
    ((c.character (-1) : ℂ) ^ (t + 1)) *
        (detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) *
          realAdjacentWeylSign (t + 1 + q) c * C) =
      ((c.character ((-1 : ℝˣ) ^ (t + 1 + q + 1)) : ℂ) * realAdjacentWeylSign (t + 1 + q) c.inverse * C) *
        detCharacter c.inverse.character.toMonoidHom (weylLong (q + 1) ℝ) := by
  rw [weylSign_inverse]
  have hw : detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) =
      (c.character (-1) : ℂ) ^ (q + 1) * (c.character (determinant (weylLong (q + 1) ℝ)) : ℂ) := by
    change (c.character (determinant (weylLong (q + 1 + 1) ℝ)) : ℂ) = _
    rw [Langlands.RankinSelberg.RankOneGammaTwist.determinant_weylLong_succ, map_mul, map_pow,
      Units.val_mul, Units.val_pow_eq_pow_val]
  have hS : detCharacter c.inverse.character.toMonoidHom (weylLong (q + 1) ℝ) =
      (c.character (determinant (weylLong (q + 1) ℝ)) : ℂ) := by
    change (c.inverse.character (determinant (weylLong (q + 1) ℝ)) : ℂ) = _
    exact inverse_character_of_sq c _ (determinant_weylLong_sq _)
  have hn : (c.character ((-1 : ℝˣ) ^ (t + 1 + q + 1)) : ℂ) = (c.character (-1) : ℂ) ^ (t + 1 + q + 1) := by
    rw [map_pow, Units.val_pow_eq_pow_val]
  rw [hw, hS, hn]
  ring

private theorem determinant_cons (c : RealCharacterData) (ds : List RealBlock) :
    (RealJacquet.determinant (RealBlock.character c :: ds) (-1) : ℂ) =
      (c.character (-1) : ℂ) * (RealJacquet.determinant ds (-1) : ℂ) := by
  change (((RealBlock.character c).determinant (-1) * (ds.map fun d => d.determinant (-1)).prod : ℂˣ) : ℂ) = _
  rw [Units.val_mul]
  rfl

/-- The reflection factor of the larger list factors through the adjoining phase. -/
private theorem pairReflectionFactor_cons (t : ℕ) (c : RealCharacterData) (ds es : List RealBlock)
    (a : ℝˣ) (sc : ℝ≥0) (hsc : 0 < sc) (s : ℂ) :
    ((c.character (-1) : ℂ) ^ (t + 1)) *
        pairReflectionFactor ds es a sc hsc
          ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) * (RealJacquet.determinant es (-1) : ℂ)) s *
        pairReflectionFactor [RealBlock.character c] es a sc hsc 1 s =
      pairReflectionFactor (RealBlock.character c :: ds) es a sc hsc
        ((RealJacquet.determinant (RealBlock.character c :: ds) (-1) : ℂ) ^ (t + 1) *
          (RealJacquet.determinant es (-1) : ℂ)) s := by
  unfold pairReflectionFactor
  rw [RealJacquet.realPairEpsilon_cons (RealBlock.character c) ds es, Units.val_mul, determinant_cons, mul_pow]
  ring

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "LowerIndex" => t + 1 + q
local notation "Rank" => t + 1 + q + 1
local notation "TailSize" => q + 1
local notation "H" => G Small
local notation "Ord" => Q t × (Outer Small q × Unip TailSize)
local notation "Dual" => Q t × (Outer Small q × (M q Small × Unip TailSize))
local notation "O" => Matrix.unitaryGroup (Fin (t + 1)) ℝ

/-- The leading square tests of the split monomial factors have finite-dimensional left
translates under the orthogonal group. -/
private theorem leading_finite (d : Coordinates Rank Rank →₀ ℕ) (c₀ : ℂ) (φ : 𝓢(Fin Rank → ℝ, ℂ))
    (p : Outer Small q) (Z : Unip TailSize) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun u : O => fun X : M Small Small =>
        leadingRestriction Small TailSize Small (retainedTail Small q p Z) (gaussianFactors Small q d c₀ φ).leading
          ((((Unitary.toUnits u : H))⁻¹).val * X))) := by
  let K := Submodule.span ℂ (Set.range fun u : unitaryCompact ℝ Small => fun X : M Small Small =>
    leadingRestriction Small TailSize Small (retainedTail Small q p Z) (gaussianFactors Small q d c₀ φ).leading
      (u⁻¹.val.val * X))
  have hK : FiniteDimensional ℂ K := RealGapLeadingCompact.realGapLeadingCompact Small q p Z _
  refine Submodule.finiteDimensional_of_le (Submodule.span_mono ?_ : _ ≤ K)
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨Unitary.toUnits u, u.property⟩, rfl⟩

/-- For a rotated split Gaussian monomial value built on a value of a uniform Whittaker map of a
character list of rank `t + 1 + q + 1`, and a value of a uniform map of a character list of rank
`t + 1`, the normalized equation at the smaller gap gives the normalized equation at the larger
gap. -/
def RealGapMonomialGrowthStatement : Prop :=
  RealLocalUnequalCharacterGrowthAtRanks LowerIndex t (rankLT t q) →
  ∀ (cs fs : List RealCharacterData), cs.length = Rank → fs.length = Small →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData LowerIndex)
    (c : RealCharacterData)
    (A : Std Rank (cs.map RealBlock.character) →ₗ[ℂ] (G Rank → ℂ)),
      IsRealUniformWhittakerIntertwiner LowerIndex (cs.map RealBlock.character) (-a) A →
    ∀ (u : Std Rank (cs.map RealBlock.character)) (d : Coordinates Rank Rank →₀ ℕ) (c₀ : ℂ)
      (φ : 𝓢(Fin Rank → ℝ, ℂ))
      (B : Std Small (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
      IsRealUniformWhittakerIntertwiner t (fs.map RealBlock.character) a B →
    ∀ v : Std Small (fs.map RealBlock.character),
      let W := rotatedValue t q a D' c (gaussianPolynomial (MvPolynomial.monomial d c₀))
        (gaussianFactors Small q d c₀ φ) (A u)
      let ds := RealBlock.character c :: cs.map RealBlock.character
      let es := fs.map RealBlock.character
      HasRealPairNormalizedGrowth ds es (ds.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock) a (NNReal.sqrt ‖(a : ℝ)‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
        ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) * (RealJacquet.determinant es (-1) : ℂ))
        (realUnequalIntegral (rankLT t (q + 1)) D W (B v))
        (realUnequalDualIntegral (rankLT t (q + 1)) (-a) D W (B v))

set_option maxHeartbeats 3000000 in
theorem realGapMonomialGrowth : RealGapMonomialGrowthStatement t q := by
  intro hLower cs fs hcs hfs a D D' c A hA u d c₀ φ B hB v W ds es
  let ds₀ := cs.map RealBlock.character
  let F := gaussianPolynomial (MvPolynomial.monomial d c₀)
  let T := gaussianFactors Small q d c₀ φ
  have hF : ∀ X, F X = T.squareEval Small q X := gaussianPolynomial_eval_factors Small q d c₀ φ
  let U := A u
  let V := B v
  have hU : U ∈ realUniformWhittakerModel LowerIndex ds₀ (-a) := mem_model hA u
  have hV : V ∈ realUniformWhittakerModel t es a := mem_model hB v
  have hUd : ArchimedeanLocal.dualFunction Rank U ∈
      realUniformWhittakerModel LowerIndex (dualCharacterBlocks cs) a := by
    simpa only [neg_neg] using realUniformWhittakerCharacterDual LowerIndex cs hcs (-a) U hU
  have hVd : ArchimedeanLocal.dualFunction Small V ∈
      realUniformWhittakerModel t (dualCharacterBlocks fs) (-a) :=
    realUniformWhittakerCharacterDual t fs hfs a V hV
  let : CompactSpace (KU Rank) := Langlands.Archimedean.RealPrincipalSeriesDuality.compactSpace_unitaryCompact _
  let κ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (KU Rank))
  have hκ : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let : κ.IsHaarMeasure := hκ
  let : IsProbabilityMeasure κ := isProbabilityMeasure_haarMeasure_top
  have hκinv : κ.IsInvInvariant := isInvInvariant_of_compact κ
  let η₁ := D.groupHaar
  have hη₁ : η₁.IsHaarMeasure := D.groupHaar_isHaar
  let : η₁.IsHaarMeasure := hη₁
  obtain ⟨C, _, hExact⟩ := realGapExactRestriction t q a D' η₁ κ hη₁ hκ hκinv
  have hE := hExact ds₀ (dualCharacterBlocks cs) c F T hF U hU hUd
  let Co := detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) * realAdjacentWeylSign (t + 1 + q) c *
    (C : ℂ)
  let Cd := (c.character ((-1 : ℝˣ) ^ Rank) : ℂ) * realAdjacentWeylSign (t + 1 + q) c.inverse * (C : ℂ)
  obtain ⟨hFo, σo, hOrd⟩ := realGapOrdinaryMellin t q D a η₁ κ hη₁ hκ Co c T ds₀ es U V hU hV W
    (fun g => ((hE g).1.2).trans (by ring))
  obtain ⟨hFd, σd, hDual⟩ := realGapDualMellin t q D a η₁ κ hη₁ hκ hκinv Cd c T F hF ds₀ es
    (dualCharacterBlocks cs) (dualCharacterBlocks fs) U V W hU hV hUd hVd
    (fun g x => (((hE g).2 x).2).trans (by unfold dualChartMeasure; ring))
  let μo := D.measure.prod (ordinaryChartMeasure t q a η₁ κ)
  let μd := D.measure.prod (dualChartMeasure t q a η₁ κ)
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : SigmaFinite (ordinaryChartMeasure t q a η₁ κ) := sigmaFinite_ordinaryChartMeasure t q a η₁ κ
  let : SigmaFinite (dualChartMeasure t q a η₁ κ) := sigmaFinite_dualChartMeasure t q a η₁ κ
  let σ := max σo σd
  let δo (p : Ord) := quotientDetAbs p.1
  let ηo (p : Ord) := δ p.2.1.1.1.1
  let δd (p : Dual) := quotientDetAbs p.1
  let ηd := dualLeadingDet t q
  let F₀ := ordinarySeparatedKernel t q false a c T U V (fun _ => 1) (fun _ => 1)
  let Fd₀ := dualSeparatedKernel t q a c T U V (fun _ => 1) (fun _ => 1)
  let Fo (p : Ord) := Co * F₀ p
  let Fd (p : Dual) := Cd * Fd₀ p
  have hηo : Measurable ηo := by
    have hLead : Continuous (fun p : Ord => p.2.1.1.1.1) := by fun_prop
    exact ((Units.continuous_val.comp hLead).matrix_det.abs).measurable
  have hMo (z : ℝ) (hz : σ ≤ z) : Integrable (fun p => ‖Fo p‖ * (δo p * ηo p) ^ z) μo := by
    have h := (hOrd (z : ℂ) (by simpa using (le_max_left σo σd).trans hz)).1.const_mul ‖Co‖
    simpa only [Fo, norm_mul, mul_assoc, Complex.ofReal_re, ordinaryProductDet, δo, ηo] using h
  have hMd (z : ℝ) (hz : σ ≤ z) : Integrable (fun p => ‖Fd p‖ * (δd p * ηd p) ^ z) μd := by
    have h := (hDual (z : ℂ) (by simpa using (le_max_right σo σd).trans hz)).1.const_mul ‖Cd‖
    simpa only [Fd, norm_mul, mul_assoc, Complex.ofReal_re, dualProductDet, δd, ηd] using h
  let sc := NNReal.sqrt ‖(a : ℝ)‖₊
  have hsc : 0 < sc := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
  let sign₁ := (RealJacquet.determinant ds₀ (-1) : ℂ) ^ (t + 1) * (RealJacquet.determinant es (-1) : ℂ)
  let phase := (c.character (-1) : ℂ) ^ (t + 1)
  have hSign : (RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) * (RealJacquet.determinant es (-1) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)
  refine realGapGrowthFromSeparatedTheta μo μd Fo Fd δo ηo δd ηd
    (hFo.const_mul Co) (hFd.const_mul Cd) (continuous_quotientDetAbs.measurable.comp measurable_fst)
    hηo (continuous_quotientDetAbs.measurable.comp measurable_fst) (measurable_dualLeadingDet t q)
    (fun p => quotientDetAbs_pos p.1) (fun p => abs_pos.mpr (p.2.1.1.1.1 : H).det_ne_zero)
    (fun p => quotientDetAbs_pos p.1) (dualLeadingDet_pos t q) σ hMo hMd sc hsc phase
    (RealBlock.character c) (RealLocalJacquet.dualBlock (RealBlock.character c)) ds₀ es
    (ds₀.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) a a a _ sign₁ 1 hSign
    (pairReflectionFactor_cons t c ds₀ es a sc hsc) ?_ _ _ ?_
  · intro b c' hb hc'
    let w₁ := ordinaryWeight ds₀ es a sc hsc sign₁ (1 / 2) 0
    let w₂ := ordinaryWeight [RealBlock.character c] es a sc hsc 1 (1 / 2) 0
    let wd₁ := reflectedWeight (ds₀.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) (1 / 2) 0
    let wd₂ := reflectedWeight [RealLocalJacquet.dualBlock (RealBlock.character c)]
      (es.map RealLocalJacquet.dualBlock) (1 / 2) 0
    let f₁ (x : ℝ) := w₁ (b * x)
    let f₂ (x : ℝ) := w₂ (c' * x)
    let k₁ (x : ℝ) := wd₁ (b⁻¹ * x)
    let k₂ (x : ℝ) := wd₂ (c'⁻¹ * x)
    let Fs := ordinarySeparatedKernel t q false a c T U V f₁ f₂
    let Fm := ordinarySeparatedKernel t q true a c T U V f₁ k₂
    let F' := dualSeparatedKernel t q a c T U V k₁ k₂
    obtain ⟨hw₁m, hwd₁m, hw₁, hwd₁, _, _⟩ :=
      realWeights_data ds₀ es (ds₀.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) a sc hsc
        sign₁ (rate := 1 / 2) (by norm_num) 0
    obtain ⟨hw₂m, hwd₂m, hw₂, hwd₂, _, _⟩ :=
      realWeights_data [RealBlock.character c] es [RealLocalJacquet.dualBlock (RealBlock.character c)]
        (es.map RealLocalJacquet.dualBlock) a sc hsc 1 (rate := 1 / 2) (by norm_num) 0
    have hf₁m : Measurable f₁ := hw₁m.comp (measurable_const.mul measurable_id)
    have hf₂m : Measurable f₂ := hw₂m.comp (measurable_const.mul measurable_id)
    have hk₁m : Measurable k₁ := hwd₁m.comp (measurable_const.mul measurable_id)
    have hk₂m : Measurable k₂ := hwd₂m.comp (measurable_const.mul measurable_id)
    have hf₁ := rapidDecay_comp_mul_left hw₁ hb
    have hf₂ := rapidDecay_comp_mul_left hw₂ hc'
    have hk₁ := rapidDecay_comp_mul_left hwd₁ (inv_pos.mpr hb)
    have hk₂ := rapidDecay_comp_mul_left hwd₂ (inv_pos.mpr hc')
    have hFs : Integrable Fs μo :=
      integrable_ordinarySeparatedKernel t q D a η₁ κ hη₁ hκ false c T ds₀ es U V hU hV f₁ f₂
        hf₁m hf₂m hf₁ hf₂
    have hFm : Integrable Fm μo :=
      integrable_ordinarySeparatedKernel t q D a η₁ κ hη₁ hκ true c T ds₀ es U V hU hV f₁ k₂
        hf₁m hk₂m hf₁ hk₂
    have hUcov : HasLeftCharacter (-a) U := RealGapAlternateWeighted.leftCharacter_of_mem hU
    have hVcov : HasLeftCharacter a V := RealGapAlternateWeighted.leftCharacter_of_mem hV
    have hRaw := realGapDualHaar t q D a η₁ κ hη₁ hκ hκinv (dualCharacterBlocks cs) (dualCharacterBlocks fs)
      _ _ hUd hVd c F T hF k₁ k₂ hk₁m hk₂m hk₁ hk₂
    have hF' : Integrable F' μd :=
      (realGapDualSeparation t q D a η₁ κ hη₁ hκ c F T hF U V hUcov hVcov k₁ k₂ hRaw).1
    have hN (p : Std Rank ds₀) (p' : Std Small es) :
        HasRealPairNormalizedGrowth ds₀ es (ds₀.map RealLocalJacquet.dualBlock)
          (es.map RealLocalJacquet.dualBlock) a sc hsc sign₁
          (realUnequalIntegral (rankLT t q) D (A p) (B p'))
          (realUnequalDualIntegral (rankLT t q) (-a) D (A p) (B p')) := by
      have h := hLower ds₀ es ⟨cs, rfl⟩ ⟨fs, rfl⟩
        (by rw [Langlands.Archimedean.realRank_map_character, hcs])
        (by rw [Langlands.Archimedean.realRank_map_character, hfs]) (-a) D (A p) (B p')
        (mem_model hA p) (by rw [neg_neg]; exact mem_model hB p')
      rw [neg_neg] at h
      have hscale : NNReal.sqrt ‖((-a : ℝˣ) : ℝ)‖₊ = NNReal.sqrt ‖(a : ℝ)‖₊ := by
        rw [Units.val_neg, nnnorm_neg]
      exact RealGodement.hasRealPairNormalizedGrowth_scale_congr hscale h
    let S := detCharacter c.inverse.character.toMonoidHom (weylLong TailSize ℝ)
    have hScale : S * (∫ p, Fs p ∂μo) = ((b * c' : ℝ) : ℂ) * ∫ p, F' p ∂μd :=
      realGapScaleComparison t q D a κ hκ c ds₀ (ds₀.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock) fs hfs a sc hsc sign₁ T (leading_finite t q d c₀ φ) A hA B hB hN
        u v b c' hb hc' (1 / 2) 0 (by norm_num) hFs hFm hF'
    have ho (p : Ord) : Fo p * (w₁ (b * δo p) * w₂ (c' * ηo p)) = Co * Fs p := by
      unfold Fs Fo
      rw [ordinarySeparatedKernel_mul_profiles]
      change Co * F₀ p * (f₁ (δo p) * f₂ (ηo p)) = Co * (F₀ p * (f₁ (δo p) * f₂ (ηo p)))
      exact mul_assoc _ _ _
    have hd (p : Dual) : Fd p * (wd₁ (b⁻¹ * δd p) * wd₂ (c'⁻¹ * ηd p)) = Cd * F' p := by
      unfold F' Fd
      rw [dualSeparatedKernel_mul_profiles]
      ring
    change phase * separatedTheta μo Fo δo ηo w₁ w₂ b c' =
      ((b * c' : ℝ) : ℂ) * separatedTheta μd Fd δd ηd wd₁ wd₂ b⁻¹ c'⁻¹
    unfold separatedTheta
    simp_rw [ho, hd, integral_const_mul]
    have hPhase : phase * Co = Cd * S := phase_identity t q c (C : ℂ)
    calc
      _ = Cd * (S * ∫ p, Fs p ∂μo) := by rw [← mul_assoc, hPhase]; ring
      _ = _ := by rw [hScale]; ring
  · refine ⟨σ, fun s hs => ⟨?_, ?_⟩⟩
    · have h := (hOrd s ((le_max_left σo σd).trans hs.le)).2
      change (∫ p, (Co * F₀ p) * (ordinaryProductDet t q p : ℂ) ^ s ∂μo) = _
      simp_rw [mul_assoc Co, integral_const_mul]
      exact h.symm
    · have h := (hDual s ((le_max_right σo σd).trans hs.le)).2
      change (∫ p, (Cd * Fd₀ p) * (dualProductDet t q p : ℂ) ^ s ∂μd) = _
      simp_rw [mul_assoc Cd, integral_const_mul]
      exact h.symm

end Langlands.Global.RankinSelbergGlobal.RealGapMonomialGrowth
