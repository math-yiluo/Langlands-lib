import Langlands.Global.RankinSelberg.ComplexGapLeadingHaar
import Langlands.Global.RankinSelberg.ComplexGapNormalizedWeighted
import Langlands.Global.RankinSelberg.ComplexGapSeparatedKernels

/-! # The ordinary and mixed factors on the normalized gap chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinarySeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (det_upperUnipotent)
open Langlands.GeneralLinear (determinant determinantContinuous inverseTranspose inverseTransposeContinuous rankInclusion)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexSelfDualMeasure complexUnequalIntegrand)
open ArchimedeanMellinPair (RapidDecay)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapAlternateWeighted (leadingSide)
open ComplexGapDualArguments (tailColumn)
open ComplexGapDualChart (retainedTail)
open ComplexGapLeadingCompact (packedTail_stack)
open ComplexGapLeadingFourier (stackRows rectTransform leadingRestriction complexGapLeadingFourier)
open ComplexGapLeadingSchwartz (leadingStack matrixDecay)
open ComplexGapLeadingHaar (interchangeMiddle measurePreserving_interchangeMiddle)
open ComplexGapMatchedTests (tailFactor tailFactor_reverse)
open ComplexGapNormalizedWeighted (normalizedWeightedKernel normalizedGapMeasure complexGapNormalizedWeighted padGL_eq_rankInclusion)
open ComplexGapRankCoordinates (rankLT)
open ComplexGapSeparatedKernels (retainedCoefficient)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest leadingSquareTest_apply leadingSquareTest_fourier)
open ComplexGapSplitFourier (columnTransform columnTransform_apply)
open ComplexGapTailExchange (SplitTailTest alternateBlockTailKernel fixedTailFactor alternateKernel_eq)
open ComplexGapTriangularChart (Outer outerMeasure)
open ComplexGapColumnFourier (triangularFourier)
open ComplexGapUnitDeterminant (unitRetained normalizedAbs_unitRetained continuous_unitRetained unitOuterMeasure)
open ComplexGapUpperTail (packedTail)
open ComplexGapWeylRestriction (reverseTail)
open ComplexGodement (characterWeight continuous_characterWeight norm_characterWeight normPower)
open ComplexGodementFourier (fourier rectFourier)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexUnequalMellinReduction (quotientDetAbs sigmaFinite_quotient)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary)
open ComplexAdjacentUnfolding (splitSquareTransform)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "SD" => complexSelfDualMeasure
local notation "ρ" => ArchimedeanLocal.translateFunction

variable (t q : ℕ)
local notation "k" => t + 1
local notation "TailSize" => q + 1
local notation "UpperIndex" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "X" => M TailSize k
local notation "Side" => Outer k q × Unip TailSize
local notation "Joint" => Q t × (X × Side)
local notation "ι" => inverseTranspose n ℂ
local notation "ι₁" => inverseTranspose k ℂ
local notation "Incl" => (rankInclusion (R := ℂ) TailSize : H →* G n)
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "RT" => fun T => reverseTail k q T

open scoped Matrix.Norms.Operator in
/-- The leading square test depends on the unit determinant matrix before the packed tail. -/
theorem leadingSquareTest_retainedTail (T : GodementColumnFactors k q) (p : Outer k q) (Z : Unip TailSize) :
    leadingSquareTest t q (retainedTail k q p Z) T.leading = leadingSquareTest t q (unitRetained k q p) T.leading := by
  apply SchwartzMap.ext
  intro Y
  simp only [leadingSquareTest_apply, retainedTail, Units.val_mul, Matrix.mul_assoc, packedTail_stack]

/-- The combined tail factor and Whittaker value use the same triangular Fourier kernel as the
weighted convergence estimate. -/
theorem tailFactor_mul_whittaker (a : ℂˣ) (T : GodementColumnFactors k q) (ds : List ComplexCharacterData)
    (W : complexWhittakerModel UpperIndex ds (-a)) (g : H) (B : G n) (Z : Unip TailSize) :
    let C := B * (packedTail k q 0 Z).val
    let S := (RT T).partial k q a
    tailFactor k q a T C * W.val (Incl g * C⁻¹) =
      S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) *
        triangularFourier k q a B S.later Z * W.val (Incl g * B⁻¹) := by
  intro C S
  let S' : SplitTailTest k q := { S with leading := fun _ => 1 }
  have h := alternateKernel_eq k q a S' ds W (1 : ℂˣ →* ℂ) g 1 B Z
  unfold alternateBlockTailKernel fixedTailFactor at h
  simp only [S', one_mul, mul_one, inv_one, MonoidHom.one_apply] at h
  let product := ∏ j : Fin q, fourier a (S.later j) (tailColumn k q (ι C) j.castSucc)
  change S.first (tailColumn k q C 0) * S.lastFrequency (row C⁻¹) * W.val (Incl g * C⁻¹) * product =
    S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) * W.val (Incl g * B⁻¹) *
      triangularFourier k q a B S.later Z at h
  have htail : tailFactor k q a T C = S.first (tailColumn k q C 0) * S.lastFrequency (row C⁻¹) * product := by
    rw [tailFactor_reverse]
    simp only [product, S, GodementColumnFactors.partial, reverseTail, Fin.rev_zero, Fin.rev_last]
  rw [htail, mul_right_comm, h, mul_right_comm]

/-- The normalized determinant-one retained matrix contributes only its character. -/
theorem character_retainedTail (d : ComplexCharacterData) (p : Outer k q) (Z : Unip TailSize) :
    d.character (determinant (retainedTail k q p Z)) = d.character (determinant (unitRetained k q p)) := by
  unfold retainedTail
  have hdet : determinant (packedTail k q 0 Z).val = 1 := Units.ext (det_upperUnipotent _)
  rw [map_mul determinant, hdet, mul_one]

/-- The ordinary rectangular factor and its positive transform on the mixed side. -/
def rectangularLeading (dual : Bool) (a : ℂˣ) (T : GodementColumnFactors k q) : 𝓢(M n k, ℂ) :=
  if dual then rectTransform a T.leading else T.leading

/-- The square test appearing before or after the fixed-coefficient square reflection. -/
def squareLeading (dual : Bool) (a : ℂˣ) (T : GodementColumnFactors k q) (C : G n) : M k k → ℂ :=
  if dual then fun x => splitSquareTransform a (leadingSquareTest t q C T.leading) x
  else fun x => leadingSquareTest t q C T.leading x

/-- The determinant factors left outside the normalized Whittaker bound. -/
def chartMultiplier (dual : Bool) (d : ComplexCharacterData) (p : Outer k q) : ℂ :=
  (d.character (determinant (unitRetained k q p)) : ℂ) *
    characterWeight (if dual then d.inv else d) ((t : ℂ) / 2)
      (determinant (leadingSide dual p.1.1.1))

/-- The determinant multiplier is measurable in the outer coordinates. -/
theorem measurable_chartMultiplier (dual : Bool) (d : ComplexCharacterData) :
    Measurable (chartMultiplier t q dual d) := by
  have hc : (fun g : G n => (d.character (determinant g) : ℂ)) =
      fun g => characterWeight d 0 (determinant g) := by
    funext g
    simp [characterWeight, normPower]
  have hD : Continuous (determinant : G n → ℂˣ) := determinantContinuous.continuous
  have hB := ((continuous_characterWeight d 0).comp hD).comp (continuous_unitRetained k q)
  have hZ : Continuous (fun p : Outer k q => leadingSide dual p.1.1.1) := by
    cases dual
    · exact continuous_fst.comp (continuous_fst.comp continuous_fst)
    · exact (inverseTransposeContinuous k ℂ).continuous.comp (continuous_fst.comp (continuous_fst.comp continuous_fst))
  unfold chartMultiplier
  change Measurable (fun p => ((fun g : G n => (d.character (determinant g) : ℂ)) (unitRetained k q p)) * _)
  rw [hc]
  exact (hB.mul ((continuous_characterWeight _ _).comp (determinantContinuous.continuous.comp hZ))).measurable

/-- Its norm is exactly a real power of the leading determinant. -/
theorem norm_chartMultiplier (dual : Bool) (d : ComplexCharacterData) (p : Outer k q) :
    ‖chartMultiplier t q dual d p‖ = δ (leadingSide dual p.1.1.1) ^
      ((if dual then d.inv else d).exponent + (t : ℂ) / 2).re := by
  have hc : ‖(d.character (determinant (unitRetained k q p)) : ℂ)‖ = 1 := by
    have he := norm_characterWeight d 0 (determinant (unitRetained k q p))
    have hB := normalizedAbs_unitRetained k q (Nat.succ_pos t) p
    change complexNormalizedAbs (determinant (unitRetained k q p) : ℂˣ).val = 1 at hB
    rw [hB, Real.one_rpow] at he
    simpa [characterWeight, normPower] using he
  unfold chartMultiplier
  rw [norm_mul, hc, one_mul, norm_characterWeight]
  rfl

/-- The alternate chart for the ordinary and mixed comparisons, with the rectangle visible. -/
def comparisonChartKernel (dual : Bool) (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Joint) : ℂ :=
  normalizedWeightedKernel dual a (rectangularLeading t q dual a T) (T.tail (Fin.last (q + 1)))
    (columnTransform a (T.tail 0)) ((RT T).partial k q a).later W V 0 f₁ f₂ (chartMultiplier t q dual d) p

/-- The chart kernel after the leading rectangle is integrated. The smaller quotient factor
stays ordinary on both sides of the square functional equation. -/
def ordinarySeparatedKernel (dual : Bool) (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Q t × Side) : ℂ :=
  let h := p.2.1.1.1.1
  let C := retainedTail k q p.2.1 p.2.2
  retainedCoefficient t q a d T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W) (ρ h V) f₁ p.1 *
    squareKernel (if dual then d.inv else d) (squareLeading t q dual a T C) (fun _ => 1) 0 (leadingSide dual h) *
    f₂ (δ (leadingSide dual h))

/-- The complementary measure is a point mass on the ordinary side and additive Haar on the mixed side. -/
def comparisonRectangleMeasure (dual : Bool) (a : ℂˣ) : Measure X :=
  if dual then rectangularMeasure (SD a) TailSize k else Measure.dirac 0

/-- The chart measure after the leading rectangle integration. -/
def ordinaryChartMeasure (a : ℂˣ) (κ : Measure (KU n)) : Measure Side :=
  (unitOuterMeasure k q (SD a) κ).prod (entryHaar (SD a) TailSize)

/-- The ordinary chart measure is sigma finite for compact Haar measure on the unitary group. -/
theorem sigmaFinite_ordinaryChartMeasure (a : ℂˣ) (κ : Measure (KU n)) [κ.IsHaarMeasure] :
    SigmaFinite (ordinaryChartMeasure t q a κ) := by
  let : CompactSpace (KU n) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : (SD a).measure.IsAddHaarMeasure := (SD a).isAddHaar
  let : SigmaFinite (SD a).measure := inferInstance
  let : SigmaFinite (entryHaar (SD a) TailSize) := entryHaar_sigmaFinite (SD a) TailSize
  let : SigmaFinite (outerMeasure k q (SD a) κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite (unitOuterMeasure k q (SD a) κ) := SigmaFinite.withDensity _
  unfold ordinaryChartMeasure
  infer_instance

private theorem leadingStack_eq (H₀ : M k k) (Y : X) : leadingStack H₀ Y = stackRows k TailSize k H₀ Y := by
  funext i j
  refine Fin.addCases (m := k) (fun i₀ => ?_) (fun i₁ => ?_) i
  · simp [leadingStack, ComplexGapLeadingFourier.stackRows_left]
  · simp [leadingStack, ComplexGapLeadingFourier.stackRows_right]

private theorem comparisonChartKernel_eq (dual : Bool) (a : ℂˣ) (d : ComplexCharacterData)
    (T : GodementColumnFactors k q) {ds : List ComplexCharacterData}
    (W : complexWhittakerModel UpperIndex ds (-a)) (V : H → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Joint) :
    let B := unitRetained k q p.2.2.1
    let h := p.2.2.1.1.1.1
    let C := retainedTail k q p.2.2.1 p.2.2.2
    comparisonChartKernel t q dual a d T W.val V f₁ f₂ p =
      rectangularLeading t q dual a T ((leadingSide dual B).val * stackRows k TailSize k (leadingSide dual h).val p.2.1) *
        (retainedCoefficient t q a d T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W.val) (ρ h V) f₁ p.1 *
          characterWeight (if dual then d.inv else d) ((t : ℂ) / 2) (determinant (leadingSide dual h)) *
          f₂ (δ (leadingSide dual h))) := by
  intro B h C
  let F := rectangularLeading t q dual a T
    ((leadingSide dual B).val * stackRows k TailSize k (leadingSide dual h).val p.2.1)
  let S := (RT T).partial k q a
  let g := p.1.out
  let T₀ := triangularFourier k q a B S.later p.2.2.2
  let χ := characterWeight (if dual then d.inv else d) ((t : ℂ) / 2) (determinant (leadingSide dual h))
  have ht := tailFactor_mul_whittaker t q a T ds W g B p.2.2.2
  dsimp only at ht
  change tailFactor k q a T C * W.val (Incl g * C⁻¹) =
    S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) * T₀ * W.val (Incl g * B⁻¹) at ht
  let gpad := padGL (Nat.le_of_lt (Nat.succ_lt_succ (rankLT t q))) g
  have hpad : gpad = Incl g := padGL_eq_rankInclusion k q g
  have hχ : d.character (determinant C) = d.character (determinant B) :=
    character_retainedTail t q d p.2.2.1 p.2.2.2
  unfold comparisonChartKernel normalizedWeightedKernel chartMultiplier retainedCoefficient weightedOrdinary
    complexUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction
  simp only [leadingStack_eq, columnTransform_apply, hχ]
  change F * T.tail (Fin.last (q + 1)) (tailColumn k q B 0) * fourier a (T.tail 0) (row B⁻¹) * T₀ *
      (W.val (gpad * B⁻¹) * V (g * h) * P g (0 - (((UpperIndex - t : ℕ) : ℂ) / 2))) *
      f₁ (quotientDetAbs p.1) * f₂ (δ (leadingSide dual h)) *
        ((d.character (determinant B) : ℂ) * χ) =
    F * (tailFactor k q a T C * (d.character (determinant B) : ℂ) *
      (W.val (gpad * C⁻¹) * V (g * h) * P g (0 - (((UpperIndex - t : ℕ) : ℂ) / 2)) *
        f₁ (quotientDetAbs p.1)) * χ * f₂ (δ (leadingSide dual h)))
  have hfirst : T.tail (Fin.last (q + 1)) (tailColumn k q B 0) = S.first (tailColumn k q B 0) := by
    simp only [S, GodementColumnFactors.partial, reverseTail, Fin.rev_zero]
  have hfreq : fourier a (T.tail 0) (row B⁻¹) = S.lastFrequency (row B⁻¹) := by
    simp only [S, GodementColumnFactors.partial, reverseTail, Fin.rev_last]
  rw [hpad, hfirst, hfreq]
  calc
    _ = F * (S.first (tailColumn k q B 0) * S.lastFrequency (row B⁻¹) * T₀ * W.val (Incl g * B⁻¹)) *
        (d.character (determinant B) : ℂ) * V (g * h) * P g (0 - (((UpperIndex - t : ℕ) : ℂ) / 2)) *
        f₁ (quotientDetAbs p.1) * f₂ (δ (leadingSide dual h)) * χ := by ring
    _ = _ := by
      rw [← ht]
      ring

set_option maxHeartbeats 800000 in
private theorem leadingFiberIntegral (dual : Bool) (a : ℂˣ) (T : GodementColumnFactors k q)
    (p : Outer k q) (Z : Unip TailSize) :
    let B := unitRetained k q p
    let h := leadingSide dual p.1.1.1
    let C := retainedTail k q p Z
    (∫ Y : X, rectangularLeading t q dual a T ((leadingSide dual B).val * stackRows k TailSize k h.val Y)
      ∂comparisonRectangleMeasure t q dual a) = squareLeading t q dual a T C h.val := by
  intro B h C
  have hlead : leadingSquareTest t q C T.leading = leadingSquareTest t q B T.leading :=
    leadingSquareTest_retainedTail t q T p Z
  cases dual
  · change (∫ Y : X, T.leading (B.val * stackRows k TailSize k h.val Y) ∂Measure.dirac 0) =
      leadingSquareTest t q C T.leading h.val
    rw [integral_dirac, hlead, leadingSquareTest_apply]
  · have hF := complexGapLeadingFourier k TailSize k a B T.leading h.val
    dsimp only at hF
    have hB : complexNormalizedAbs B.val.det = 1 := normalizedAbs_unitRetained k q (Nat.succ_pos t) p
    rw [hB, inv_one, one_pow, one_smul] at hF
    change (∫ Y : X, rectTransform a T.leading ((ι B).val * stackRows k TailSize k h.val Y)
      ∂rectangularMeasure (SD a) TailSize k) = splitSquareTransform a (leadingSquareTest t q C T.leading) h.val
    rw [hlead, leadingSquareTest_fourier]
    exact hF.symm

private theorem integrate_comparisonChartKernel (dual : Bool) (a : ℂˣ) (d : ComplexCharacterData)
    (T : GodementColumnFactors k q) {ds : List ComplexCharacterData} (W : complexWhittakerModel UpperIndex ds (-a))
    (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Q t × Side) :
    (∫ Y : X, comparisonChartKernel t q dual a d T W.val V f₁ f₂ (p.1, Y, p.2)
      ∂comparisonRectangleMeasure t q dual a) = ordinarySeparatedKernel t q dual a d T W.val V f₁ f₂ p := by
  simp_rw [comparisonChartKernel_eq t q dual a d T W V f₁ f₂]
  rw [integral_mul_const, leadingFiberIntegral]
  unfold ordinarySeparatedKernel squareKernel
  dsimp only [Prod.fst, Prod.snd]
  rw [add_zero, mul_one]
  ring

private theorem sigmaFinite_comparisonRectangleMeasure (dual : Bool) (a : ℂˣ) :
    SigmaFinite (comparisonRectangleMeasure t q dual a) := by
  cases dual
  · change SigmaFinite (Measure.dirac (0 : X))
    infer_instance
  · change SigmaFinite (rectangularMeasure (SD a) TailSize k)
    let : (rectangularMeasure (SD a) TailSize k).IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
    infer_instance

/-- The ordinary and mixed chart integrals collapse to the separated kernels. -/
def ComplexGapOrdinarySeparationStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU n)), κ.IsHaarMeasure →
    ∀ (dual : Bool) (d : ComplexCharacterData) (T : GodementColumnFactors k q) (ds : List ComplexCharacterData)
      (W : complexWhittakerModel UpperIndex ds (-a)) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ),
    let τ := normalizedGapMeasure t q a D (comparisonRectangleMeasure t q dual a) κ
    let B := D.measure.prod (ordinaryChartMeasure t q a κ)
    let F := comparisonChartKernel t q dual a d T W.val V f₁ f₂
    let Fs := ordinarySeparatedKernel t q dual a d T W.val V f₁ f₂
    Integrable F τ → Integrable Fs B ∧ (∫ p, F p ∂τ) = ∫ p, Fs p ∂B

set_option maxHeartbeats 1000000 in
theorem complexGapOrdinarySeparation : ComplexGapOrdinarySeparationStatement t q := by
  intro D a κ hκ dual d T ds W V f₁ f₂
  dsimp only
  intro hF
  let ξ := comparisonRectangleMeasure t q dual a
  let η := ordinaryChartMeasure t q a κ
  let F := comparisonChartKernel t q dual a d T W.val V f₁ f₂
  let Fs := ordinarySeparatedKernel t q dual a d T W.val V f₁ f₂
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite ξ := sigmaFinite_comparisonRectangleMeasure t q dual a
  let : SigmaFinite η := sigmaFinite_ordinaryChartMeasure t q a κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let e := interchangeMiddle (A := Q t) (B := X) (C := Side)
  have he : MeasurePreserving e ((D.measure.prod η).prod ξ) (D.measure.prod (ξ.prod η)) :=
    measurePreserving_interchangeMiddle D.measure ξ η
  let J := F ∘ e
  have hJ : Integrable J ((D.measure.prod η).prod ξ) := he.integrable_comp_of_integrable hF
  have hpt (p : Q t × Side) : (∫ Y : X, J (p, Y) ∂ξ) = Fs p :=
    integrate_comparisonChartKernel t q dual a d T W V f₁ f₂ p
  change Integrable Fs (D.measure.prod η) ∧ (∫ p, F p ∂D.measure.prod (ξ.prod η)) = ∫ p, Fs p ∂D.measure.prod η
  refine ⟨hJ.integral_prod_left.congr (ae_of_all _ hpt), ?_⟩
  calc
    _ = ∫ p, J p ∂(D.measure.prod η).prod ξ := (he.integral_comp e.measurableEmbedding F).symm
    _ = ∫ p, Fs p ∂D.measure.prod η := (integral_prod J hJ).trans (integral_congr_ae (ae_of_all _ hpt))

/-- The ordinary and mixed separated kernels are jointly integrable for independent rapid profiles. -/
theorem integrable_ordinarySeparatedKernel (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU n))
    (hκ : κ.IsHaarMeasure) (dual : Bool) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (ds es : List ComplexCharacterData) (W : complexWhittakerModel UpperIndex ds (-a)) (V : complexWhittakerModel t es a)
    (f₁ f₂ : ℝ → ℂ) (hm₁ : Measurable f₁) (hm₂ : Measurable f₂) (hf₁ : RapidDecay f₁) (hf₂ : RapidDecay f₂) :
    Integrable (ordinarySeparatedKernel t q dual a d T W.val V.val f₁ f₂)
      (D.measure.prod (ordinaryChartMeasure t q a κ)) := by
  let ξ := comparisonRectangleMeasure t q dual a
  let l := Module.finrank ℝ X + 1
  let β := ((if dual then d.inv else d).exponent + (t : ℂ) / 2).re
  have hY : Integrable (matrixDecay l : X → ℝ) ξ := by
    cases dual
    · exact integrable_dirac (by simp)
    · let ν := rectangularMeasure (SD a) TailSize k
      let : ν.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
      refine (integrable_one_add_norm (μ := ν) (r := (l : ℝ)) (by exact_mod_cast Nat.lt_succ_self _)).congr ?_
      exact ae_of_all _ fun Y => by
        simp only [matrixDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖Y‖), Real.rpow_natCast]
  have hBound (p : Outer k q) : ‖chartMultiplier t q dual d p‖ ≤
      1 * δ (leadingSide dual p.1.1.1) ^ β * Real.exp (0 * ∑ i, |p.1.1.2 i|) := by
    rw [norm_chartMultiplier, one_mul, zero_mul, Real.exp_zero, mul_one]
  have hF : Integrable (comparisonChartKernel t q dual a d T W.val V.val f₁ f₂)
      (normalizedGapMeasure t q a D ξ κ) :=
    complexGapNormalizedWeighted t q a D ξ κ hκ (sigmaFinite_comparisonRectangleMeasure t q dual a) l hY
      dual ds es W V (rectangularLeading t q dual a T) (T.tail (Fin.last (q + 1))) (columnTransform a (T.tail 0))
      ((RT T).partial k q a).later 0 f₁ f₂ (chartMultiplier t q dual d) 1 β 0 zero_le_one le_rfl
      (measurable_chartMultiplier t q dual d) hm₁ hm₂ hf₁ hf₂ hBound
  exact (complexGapOrdinarySeparation t q D a κ hκ dual d T ds W V.val f₁ f₂ hF).1

end Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinarySeparation
