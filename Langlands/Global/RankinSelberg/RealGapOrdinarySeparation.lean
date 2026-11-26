import Langlands.Global.RankinSelberg.RealGapLeadingHaar
import Langlands.Global.RankinSelberg.RealGapLeadingCompact
import Langlands.Global.RankinSelberg.RealGapNormalizedWeighted
import Langlands.Global.RankinSelberg.RealGapSeparatedKernels
import Langlands.Global.RankinSelberg.RealGapOrdinaryWeighted
import Langlands.Global.RankinSelberg.RealWhittakerTranslatedIntegrals

/-! # The ordinary and mixed factors on the normalized real gap chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapOrdinarySeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant determinantContinuous inverseTranspose inverseTransposeContinuous
  rankInclusion)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs realSelfDualMeasure realUnequalIntegrand
  realFourierTransform)
open ArchimedeanMellinPair (RapidDecay)
open RealJacquet (realAdjacentMatrixWeight detCharacter)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapAlternateWeighted (leadingSide leftCharacter_of_mem)
open RealGapColumnFourier (triangularFourier columnSchwartzFourier columnSchwartzFourier_apply)
open RealGapDualArguments (tailColumn)
open RealGapDualChart (retainedTail)
open RealGapLeadingCompact (packedTail_stack)
open RealGapLeadingFourier (stackRows rectTransform rectFourier leadingRestriction leadingRestriction_apply
  realGapLeadingFourier)
open RealGapLeadingSchwartz (leadingStack matrixDecay)
open RealGapLeadingHaar (interchangeMiddle measurePreserving_interchangeMiddle)
open RealGapMatchedTests (tailFactor tailFactor_reverse)
open RealGapNormalizedWeighted (normalizedWeightedKernel normalizedGapMeasure realGapNormalizedWeighted
  padGL_eq_rankInclusion)
open RealGapOrdinaryWeighted (continuous_detPower continuous_detCharacter norm_detPower norm_detCharacter)
open RealGapRankCoordinates (rankLT)
open RealGapSeparatedKernels (retainedCoefficient)
open RealGapTailExchange (SplitTailTest LeftWhittakerEquivariant alternateBlockTailKernel fixedTailFactor
  alternateKernel_eq)
open RealGapTriangularChart (Outer outerMeasure)
open RealGapUnitDeterminant (unitRetained normalizedAbs_unitRetained continuous_unitRetained unitOuterMeasure)
open RealGapUpperTail (packedTail)
open RealGapWeylRestriction (reverseTail)
open RealGodement (realRectangularSchwartzFourier)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealUnequalMellinReduction (quotientDetAbs sigmaFinite_quotient)
open RealWhittakerTranslatedIntegrals (weightedOrdinary)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "SD" => realSelfDualMeasure
local notation "ρ" => ArchimedeanLocal.translateFunction

local instance gapOrdinarySeparationGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapOrdinarySeparationGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapOrdinarySeparationGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapOrdinarySeparationGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapOrdinarySeparationUMeasurable (n : ℕ) : MeasurableSpace (Unip n) := borel _
local instance gapOrdinarySeparationUBorel (n : ℕ) : BorelSpace (Unip n) := ⟨rfl⟩
local instance gapOrdinarySeparationQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapOrdinarySeparationQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

variable (t q : ℕ)
local notation "k" => t + 1
local notation "TailSize" => q + 1
local notation "UpperIndex" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "X" => M TailSize k
local notation "Side" => Outer k q × Unip TailSize
local notation "Joint" => Q t × (X × Side)
local notation "ι" => inverseTranspose n ℝ
local notation "ι₁" => inverseTranspose k ℝ
local notation "Incl" => (rankInclusion (R := ℝ) TailSize : H →* G n)
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "RT" => fun T => reverseTail k q T

/-- The leading square test depends on the unit determinant matrix before the packed tail. -/
theorem leadingRestriction_retainedTail (T : GodementColumnFactors k q) (p : Outer k q)
    (Z : Unip TailSize) :
    leadingRestriction k TailSize k (retainedTail k q p Z) T.leading =
      leadingRestriction k TailSize k (unitRetained k q p) T.leading := by
  apply SchwartzMap.ext
  intro Y
  simp only [leadingRestriction_apply, retainedTail, Units.val_mul, Matrix.mul_assoc, packedTail_stack]

/-- The combined tail factor and Whittaker value use the same triangular Fourier kernel as the
weighted convergence estimate. -/
theorem tailFactor_mul_whittaker (a : ℝˣ) (T : GodementColumnFactors k q) (W : G n → ℂ)
    (hW : LeftWhittakerEquivariant k q a W) (g : H) (B : G n) (Z : Unip TailSize) :
    let C := B * (packedTail k q 0 Z).val
    let S := (RT T).partial k q a
    tailFactor k q a T C * W (Incl g * C⁻¹) =
      S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) *
        triangularFourier k q a B S.later Z * W (Incl g * B⁻¹) := by
  intro C S
  let S' : SplitTailTest k q := { S with leading := fun _ => 1 }
  have h := alternateKernel_eq k q a S' W hW (1 : ℝˣ →* ℂ) g 1 B Z
  unfold alternateBlockTailKernel fixedTailFactor at h
  simp only [S', one_mul, mul_one, inv_one, MonoidHom.one_apply] at h
  let product := ∏ j : Fin q, realFourierTransform a (S.later j) (tailColumn k q (ι C) j.castSucc)
  change S.first (tailColumn k q C 0) * S.lastFrequency (row C⁻¹) * W (Incl g * C⁻¹) * product =
    S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) * W (Incl g * B⁻¹) *
      triangularFourier k q a B S.later Z at h
  have htail : tailFactor k q a T C =
      S.first (tailColumn k q C 0) * S.lastFrequency (row C⁻¹) * product := by
    rw [tailFactor_reverse]
    simp only [product, S, GodementColumnFactors.partial, reverseTail, Fin.rev_zero, Fin.rev_last]
  rw [htail, mul_right_comm, h, mul_right_comm]

/-- The normalized determinant-one retained matrix contributes only its character. -/
theorem character_retainedTail (c : RealCharacterData) (p : Outer k q) (Z : Unip TailSize) :
    detCharacter c.character.toMonoidHom (retainedTail k q p Z) =
      detCharacter c.character.toMonoidHom (unitRetained k q p) := by
  unfold retainedTail detCharacter
  have hdet : determinant (packedTail k q 0 Z).val = 1 := by
    let R := packedTail k q 0 Z
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
        Matrix.det_of_isUpperTriangular R.2.1, Finset.prod_eq_one fun i _ => R.2.2 i])
  rw [map_mul determinant, hdet, mul_one]

/-- The ordinary rectangular factor and its transform on the mixed side. -/
def rectangularLeading (dual : Bool) (a : ℝˣ) (T : GodementColumnFactors k q) : 𝓢(M n k, ℂ) :=
  if dual then rectTransform a T.leading else T.leading

/-- The square test appearing before or after the fixed-coefficient square reflection. -/
def squareLeading (dual : Bool) (a : ℝˣ) (T : GodementColumnFactors k q) (C : G n) : M k k → ℂ :=
  if dual then fun x => realRectangularSchwartzFourier a (leadingRestriction k TailSize k C T.leading) x
  else fun x => leadingRestriction k TailSize k C T.leading x

/-- The character attached to the ordinary or mixed side. -/
def sideCharacter (dual : Bool) (c : RealCharacterData) : RealCharacterData :=
  if dual then c.inverse else c

/-- The determinant factors left outside the normalized Whittaker bound. -/
def chartMultiplier (dual : Bool) (c : RealCharacterData) (p : Outer k q) : ℂ :=
  detCharacter c.character.toMonoidHom (unitRetained k q p) *
    (detCharacter (sideCharacter dual c).character.toMonoidHom (leadingSide dual p.1.1.1) *
      P (leadingSide dual p.1.1.1) ((t : ℂ) / 2))

private theorem continuous_leadingCoordinate (dual : Bool) :
    Continuous (fun p : Outer k q => leadingSide dual p.1.1.1) := by
  cases dual
  · exact continuous_fst.comp (continuous_fst.comp continuous_fst)
  · exact (inverseTransposeContinuous k ℝ).continuous.comp
      (continuous_fst.comp (continuous_fst.comp continuous_fst))

/-- The determinant multiplier is measurable in the outer coordinates. -/
theorem measurable_chartMultiplier (dual : Bool) (c : RealCharacterData) :
    Measurable (chartMultiplier t q dual c) := by
  have hZ := continuous_leadingCoordinate t q dual
  unfold chartMultiplier
  exact (((continuous_detCharacter c).comp (continuous_unitRetained k q)).mul
    (((continuous_detCharacter _).comp hZ).mul ((continuous_detPower _).comp hZ))).measurable

/-- Its norm is exactly a real power of the leading determinant. -/
theorem norm_chartMultiplier (dual : Bool) (c : RealCharacterData) (p : Outer k q) :
    ‖chartMultiplier t q dual c p‖ = δ (leadingSide dual p.1.1.1) ^
      ((sideCharacter dual c).exponent + (t : ℂ) / 2).re := by
  have hu : realNormalizedAbs (unitRetained k q p).val.det = 1 :=
    normalizedAbs_unitRetained k q (Nat.succ_pos t) p
  have hpos : 0 < δ (leadingSide dual p.1.1.1) := abs_pos.mpr (leadingSide dual p.1.1.1).det_ne_zero
  unfold chartMultiplier
  rw [norm_mul, norm_mul, norm_detCharacter, norm_detCharacter, norm_detPower]
  dsimp only
  rw [hu, Real.one_rpow, one_mul, ← Real.rpow_add hpos, Complex.add_re]

/-- The alternate chart for the ordinary and mixed comparisons, with the rectangle visible. -/
def comparisonChartKernel (dual : Bool) (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Joint) : ℂ :=
  normalizedWeightedKernel dual a (rectangularLeading t q dual a T) (T.tail (Fin.last (q + 1)))
    (columnSchwartzFourier a (T.tail 0)) ((RT T).partial k q a).later W V 0 f₁ f₂
    (chartMultiplier t q dual c) p

/-- The chart kernel after the leading rectangle is integrated. The smaller quotient factor
stays ordinary on both sides of the square functional equation. -/
def ordinarySeparatedKernel (dual : Bool) (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Q t × Side) : ℂ :=
  let h := p.2.1.1.1.1
  let C := retainedTail k q p.2.1 p.2.2
  retainedCoefficient t q a c T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W) (ρ h V) f₁ p.1 *
    realAdjacentMatrixWeight (sideCharacter dual c).character.toMonoidHom (squareLeading t q dual a T C) 0
      (leadingSide dual h) *
    f₂ (δ (leadingSide dual h))

/-- The complementary measure is a point mass on the ordinary side and additive Haar on the mixed side. -/
def comparisonRectangleMeasure (dual : Bool) (a : ℝˣ) : Measure X :=
  if dual then rectangularMeasure (SD a) TailSize k else Measure.dirac 0

/-- The chart measure after the leading rectangle integration. -/
def ordinaryChartMeasure (a : ℝˣ) (η₁ : Measure H) (κ : Measure (KU n)) : Measure Side :=
  (unitOuterMeasure k q (SD a) η₁ κ).prod (entryHaar (SD a) TailSize)

/-- The ordinary chart measure is sigma finite for Haar measures. -/
theorem sigmaFinite_ordinaryChartMeasure (a : ℝˣ) (η₁ : Measure H) (κ : Measure (KU n))
    [η₁.IsHaarMeasure] [κ.IsHaarMeasure] : SigmaFinite (ordinaryChartMeasure t q a η₁ κ) := by
  let : (SD a).measure.IsAddHaarMeasure := (SD a).isAddHaar
  let : SigmaFinite (SD a).measure := inferInstance
  let : SigmaFinite (entryHaar (SD a) TailSize) := entryHaar_sigmaFinite (SD a) TailSize
  let : SecondCountableTopology (KU n) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SigmaFinite (outerMeasure k q (SD a) η₁ κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite (unitOuterMeasure k q (SD a) η₁ κ) := SigmaFinite.withDensity _
  unfold ordinaryChartMeasure
  infer_instance

private theorem leadingStack_eq (H₀ : M k k) (Y : X) :
    leadingStack H₀ Y = stackRows k TailSize k H₀ Y := by
  funext i j
  refine Fin.addCases (m := k) (fun i₀ => ?_) (fun i₁ => ?_) i
  · simp [leadingStack, RealGapLeadingFourier.stackRows_left]
  · simp [leadingStack, RealGapLeadingFourier.stackRows_right]

private theorem comparisonChartKernel_eq (dual : Bool) (a : ℝˣ) (c : RealCharacterData)
    (T : GodementColumnFactors k q) {ds : List RealBlock} (W : G n → ℂ)
    (hW : W ∈ realUniformWhittakerModel UpperIndex ds (-a)) (V : H → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Joint) :
    let B := unitRetained k q p.2.2.1
    let h := p.2.2.1.1.1.1
    let C := retainedTail k q p.2.2.1 p.2.2.2
    comparisonChartKernel t q dual a c T W V f₁ f₂ p =
      rectangularLeading t q dual a T
          ((leadingSide dual B).val * stackRows k TailSize k (leadingSide dual h).val p.2.1) *
        (retainedCoefficient t q a c T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W) (ρ h V) f₁ p.1 *
          (detCharacter (sideCharacter dual c).character.toMonoidHom (leadingSide dual h) *
            P (leadingSide dual h) ((t : ℂ) / 2)) *
          f₂ (δ (leadingSide dual h))) := by
  intro B h C
  have hWeq : LeftWhittakerEquivariant k q a W :=
    fun u hu x => ((realUniformWhittakerRegularity UpperIndex ds (-a) W hW).1 []).1 u hu x
  let F := rectangularLeading t q dual a T
    ((leadingSide dual B).val * stackRows k TailSize k (leadingSide dual h).val p.2.1)
  let S := (RT T).partial k q a
  let g := p.1.out
  let T₀ := triangularFourier k q a B S.later p.2.2.2
  let χ := detCharacter (sideCharacter dual c).character.toMonoidHom (leadingSide dual h) *
    P (leadingSide dual h) ((t : ℂ) / 2)
  have ht := tailFactor_mul_whittaker t q a T W hWeq g B p.2.2.2
  dsimp only at ht
  change tailFactor k q a T C * W (Incl g * C⁻¹) =
    S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) * T₀ * W (Incl g * B⁻¹) at ht
  let gpad := padGL (Nat.le_of_lt (Nat.succ_lt_succ (rankLT t q))) g
  have hpad : gpad = Incl g := padGL_eq_rankInclusion k q g
  have hχ : detCharacter c.character.toMonoidHom C = detCharacter c.character.toMonoidHom B :=
    character_retainedTail t q c p.2.2.1 p.2.2.2
  unfold comparisonChartKernel normalizedWeightedKernel chartMultiplier retainedCoefficient weightedOrdinary
    realUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction
  simp only [leadingStack_eq, columnSchwartzFourier_apply, hχ]
  change F * T.tail (Fin.last (q + 1)) (tailColumn k q B 0) *
      realFourierTransform a (T.tail 0) (row B⁻¹) * T₀ *
      (W (gpad * B⁻¹) * V (g * h) * P g (0 - (((UpperIndex - t : ℕ) : ℂ) / 2))) *
      f₁ (quotientDetAbs p.1) * f₂ (δ (leadingSide dual h)) *
        (detCharacter c.character.toMonoidHom B * χ) =
    F * (tailFactor k q a T C * detCharacter c.character.toMonoidHom B *
      (W (gpad * C⁻¹) * V (g * h) * P g (0 - (((UpperIndex - t : ℕ) : ℂ) / 2)) *
        f₁ (quotientDetAbs p.1)) * χ * f₂ (δ (leadingSide dual h)))
  have hfirst : T.tail (Fin.last (q + 1)) (tailColumn k q B 0) = S.first (tailColumn k q B 0) := by
    simp only [S, GodementColumnFactors.partial, reverseTail, Fin.rev_zero]
  have hfreq : realFourierTransform a (T.tail 0) (row B⁻¹) = S.lastFrequency (row B⁻¹) := by
    simp only [S, GodementColumnFactors.partial, reverseTail, Fin.rev_last]
  rw [hpad, hfirst, hfreq]
  calc
    _ = F * (S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) * T₀ * W (Incl g * B⁻¹)) *
        detCharacter c.character.toMonoidHom B * V (g * h) *
        P g (0 - (((UpperIndex - t : ℕ) : ℂ) / 2)) *
        f₁ (quotientDetAbs p.1) * f₂ (δ (leadingSide dual h)) * χ := by ring
    _ = _ := by
      rw [← ht]
      ring

set_option maxHeartbeats 800000 in
private theorem leadingFiberIntegral (dual : Bool) (a : ℝˣ) (T : GodementColumnFactors k q)
    (p : Outer k q) (Z : Unip TailSize) :
    let B := unitRetained k q p
    let h := leadingSide dual p.1.1.1
    let C := retainedTail k q p Z
    (∫ Y : X, rectangularLeading t q dual a T ((leadingSide dual B).val * stackRows k TailSize k h.val Y)
      ∂comparisonRectangleMeasure t q dual a) = squareLeading t q dual a T C h.val := by
  intro B h C
  have hlead : leadingRestriction k TailSize k C T.leading = leadingRestriction k TailSize k B T.leading :=
    leadingRestriction_retainedTail t q T p Z
  cases dual
  · change (∫ Y : X, T.leading (B.val * stackRows k TailSize k h.val Y) ∂Measure.dirac 0) =
      leadingRestriction k TailSize k C T.leading h.val
    rw [integral_dirac, hlead, leadingRestriction_apply]
    rfl
  · have hF := realGapLeadingFourier k TailSize k a B T.leading h.val
    have hB : realNormalizedAbs B.val.det = 1 := normalizedAbs_unitRetained k q (Nat.succ_pos t) p
    rw [hB, inv_one, one_pow, one_smul] at hF
    change (∫ Y : X, rectTransform a T.leading ((ι B).val * stackRows k TailSize k h.val Y)
      ∂rectangularMeasure (SD a) TailSize k) =
        realRectangularSchwartzFourier a (leadingRestriction k TailSize k C T.leading) h.val
    rw [hlead]
    have hι : (ι B).val = B⁻¹.val.transpose := rfl
    rw [hι]
    have hR : rectFourier a (leadingRestriction k TailSize k B T.leading) h.val =
        realRectangularSchwartzFourier a (leadingRestriction k TailSize k B T.leading) h.val := by
      rw [← RealGapLeadingFourier.rectTransform_apply]
      rfl
    exact hF.symm.trans hR

private theorem integrate_comparisonChartKernel (dual : Bool) (a : ℝˣ) (c : RealCharacterData)
    (T : GodementColumnFactors k q) {ds : List RealBlock} (W : G n → ℂ)
    (hW : W ∈ realUniformWhittakerModel UpperIndex ds (-a))
    (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Q t × Side) :
    (∫ Y : X, comparisonChartKernel t q dual a c T W V f₁ f₂ (p.1, Y, p.2)
      ∂comparisonRectangleMeasure t q dual a) = ordinarySeparatedKernel t q dual a c T W V f₁ f₂ p := by
  simp_rw [comparisonChartKernel_eq t q dual a c T W hW V f₁ f₂]
  rw [integral_mul_const, leadingFiberIntegral]
  unfold ordinarySeparatedKernel realAdjacentMatrixWeight
  dsimp only [Prod.fst, Prod.snd]
  rw [zero_add]
  ring

private theorem sigmaFinite_comparisonRectangleMeasure (dual : Bool) (a : ℝˣ) :
    SigmaFinite (comparisonRectangleMeasure t q dual a) := by
  cases dual
  · change SigmaFinite (Measure.dirac (0 : X))
    infer_instance
  · change SigmaFinite (rectangularMeasure (SD a) TailSize k)
    let : (rectangularMeasure (SD a) TailSize k).IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
    infer_instance

/-- The ordinary and mixed chart integrals collapse to the separated kernels. -/
def RealGapOrdinarySeparationStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H) (κ : Measure (KU n)),
    η₁.IsHaarMeasure → κ.IsHaarMeasure →
    ∀ (dual : Bool) (c : RealCharacterData) (T : GodementColumnFactors k q) (ds : List RealBlock)
      (W : G n → ℂ), W ∈ realUniformWhittakerModel UpperIndex ds (-a) →
    ∀ (V : H → ℂ) (f₁ f₂ : ℝ → ℂ),
    let τ := normalizedGapMeasure t q a D (comparisonRectangleMeasure t q dual a) η₁ κ
    let B := D.measure.prod (ordinaryChartMeasure t q a η₁ κ)
    let F := comparisonChartKernel t q dual a c T W V f₁ f₂
    let Fs := ordinarySeparatedKernel t q dual a c T W V f₁ f₂
    Integrable F τ → Integrable Fs B ∧ (∫ p, F p ∂τ) = ∫ p, Fs p ∂B

set_option maxHeartbeats 1000000 in
theorem realGapOrdinarySeparation : RealGapOrdinarySeparationStatement t q := by
  intro D a η₁ κ hη₁ hκ dual c T ds W hW V f₁ f₂
  dsimp only
  intro hF
  let ξ := comparisonRectangleMeasure t q dual a
  let η := ordinaryChartMeasure t q a η₁ κ
  let F := comparisonChartKernel t q dual a c T W V f₁ f₂
  let Fs := ordinarySeparatedKernel t q dual a c T W V f₁ f₂
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite ξ := sigmaFinite_comparisonRectangleMeasure t q dual a
  let : SigmaFinite η := sigmaFinite_ordinaryChartMeasure t q a η₁ κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let e := interchangeMiddle (A := Q t) (B := X) (C := Side)
  have he : MeasurePreserving e ((D.measure.prod η).prod ξ) (D.measure.prod (ξ.prod η)) :=
    measurePreserving_interchangeMiddle D.measure ξ η
  let J := F ∘ e
  have hJ : Integrable J ((D.measure.prod η).prod ξ) := he.integrable_comp_of_integrable hF
  have hpt (p : Q t × Side) : (∫ Y : X, J (p, Y) ∂ξ) = Fs p :=
    integrate_comparisonChartKernel t q dual a c T W hW V f₁ f₂ p
  change Integrable Fs (D.measure.prod η) ∧ (∫ p, F p ∂D.measure.prod (ξ.prod η)) =
    ∫ p, Fs p ∂D.measure.prod η
  refine ⟨hJ.integral_prod_left.congr (ae_of_all _ hpt), ?_⟩
  calc
    _ = ∫ p, J p ∂(D.measure.prod η).prod ξ := (he.integral_comp e.measurableEmbedding F).symm
    _ = ∫ p, Fs p ∂D.measure.prod η :=
      (integral_prod J hJ).trans (integral_congr_ae (ae_of_all _ hpt))

/-- The ordinary and mixed separated kernels are jointly integrable for independent rapid profiles. -/
theorem integrable_ordinarySeparatedKernel (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H)
    (κ : Measure (KU n)) (hη₁ : η₁.IsHaarMeasure) (hκ : κ.IsHaarMeasure) (dual : Bool)
    (c : RealCharacterData) (T : GodementColumnFactors k q) (ds es : List RealBlock)
    (W : G n → ℂ) (V : H → ℂ) (hW : W ∈ realUniformWhittakerModel UpperIndex ds (-a))
    (hV : V ∈ realUniformWhittakerModel t es a)
    (f₁ f₂ : ℝ → ℂ) (hm₁ : Measurable f₁) (hm₂ : Measurable f₂) (hf₁ : RapidDecay f₁)
    (hf₂ : RapidDecay f₂) :
    Integrable (ordinarySeparatedKernel t q dual a c T W V f₁ f₂)
      (D.measure.prod (ordinaryChartMeasure t q a η₁ κ)) := by
  let ξ := comparisonRectangleMeasure t q dual a
  let l := Module.finrank ℝ X + 1
  let β := ((sideCharacter dual c).exponent + (t : ℂ) / 2).re
  have hY : Integrable (matrixDecay l : X → ℝ) ξ := by
    cases dual
    · exact integrable_dirac (by simp)
    · let ν := rectangularMeasure (SD a) TailSize k
      let : ν.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
      refine (integrable_one_add_norm (μ := ν) (r := (l : ℝ))
        (by exact_mod_cast Nat.lt_succ_self _)).congr ?_
      exact ae_of_all _ fun Y => by
        simp only [matrixDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖Y‖), Real.rpow_natCast]
  have hBound (p : Outer k q) : ‖chartMultiplier t q dual c p‖ ≤
      1 * δ (leadingSide dual p.1.1.1) ^ β * Real.exp (0 * ∑ i, |p.1.1.2 i|) := by
    rw [norm_chartMultiplier, one_mul, zero_mul, Real.exp_zero, mul_one]
  have hF : Integrable (comparisonChartKernel t q dual a c T W V f₁ f₂)
      (normalizedGapMeasure t q a D ξ η₁ κ) :=
    realGapNormalizedWeighted t q a D ξ η₁ κ hη₁ hκ (sigmaFinite_comparisonRectangleMeasure t q dual a) l hY
      dual ds es W V hW hV (rectangularLeading t q dual a T) (T.tail (Fin.last (q + 1)))
      (columnSchwartzFourier a (T.tail 0)) ((RT T).partial k q a).later 0 f₁ f₂
      (chartMultiplier t q dual c) 1 β 0 zero_le_one le_rfl
      (measurable_chartMultiplier t q dual c) hm₁ hm₂ hf₁ hf₂ hBound
  exact (realGapOrdinarySeparation t q D a η₁ κ hη₁ hκ dual c T ds W hW V f₁ f₂ hF).1

end Langlands.Global.RankinSelbergGlobal.RealGapOrdinarySeparation
