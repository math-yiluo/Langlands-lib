import Langlands.Global.RankinSelberg.ArchimedeanMellinMarginal
import Langlands.Global.RankinSelberg.ComplexGapRetainedNormalization
import Langlands.Global.RankinSelberg.ComplexGapOrdinaryMellin
import Langlands.Global.RankinSelberg.ComplexGapDualMellin

/-! # The normalized ordinary integral as a retained marginal -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped Matrix.Norms.Operator SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open ArchimedeanLocal Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz)
open Langlands.HarmonicAnalysis.Distribution.RenardHecke (isInvInvariant_of_compact isProbabilityMeasure_haarMeasure_top)
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanComplexPairFactor (complexLFactor_stripExpType)
open ArchimedeanInverseMellin (StripExpType)
open ArchimedeanMellinMarginal (archimedeanMellinMarginal)
open ComplexAdjacentUnfolding (splitSquareTransform)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapAlternateWeighted (leadingSide)
open ComplexGapDualArguments (tailColumn)
open ComplexGapDualHaar (dualChartMeasure)
open ComplexGapDualSeparation (dualSeparatedKernel complexGapDualMellin dualProductDet dualProductDet_pos dualLeadingDet
  measurable_dualProductDet)
open ComplexGapExactRestriction (rotatedValue complexGapExactRestriction)
open ComplexGapLeadingHaar (Retained splitOuter outerWithLeading retainedTail_outerWithLeading retainedMeasure
  sigmaFinite_retainedMeasure complexGapLeadingHaar interchangeFirst measurePreserving_interchangeFirst)
open ComplexGapMatchedTests (tailFactor)
open ComplexGapOrdinarySeparation (ordinaryChartMeasure sigmaFinite_ordinaryChartMeasure ordinarySeparatedKernel ordinaryProductDet ordinaryProductDet_pos
  measurable_ordinaryProductDet ordinaryWeylPhase squareLeading complexGapOrdinaryMellin)
open ComplexGapRankCoordinates (rankLT rectangleRows measurePreserving_rectangleRows)
open ComplexGapSeparatedKernels (detPower_add retainedCoefficient)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest)
open ComplexGapTriangularChart (Outer)
open ComplexGodement (characterWeight normPower)
open ComplexGodementPaddedRestriction (normPower_determinant)
open ComplexGapSplitFourier (columnTransform columnTransform_apply)
open ComplexJacquet (complexCentralSign_sq)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexThetaNormalizedGrowth (stripExpType_pairReflectionFactor_inv)
open ComplexUnequalMellinReduction (sigmaFinite_quotient quotientDetAbs quotientDetAbs_pos complexUnequalIntegrand_eq_mul complexUnequalDualKernel_eq_mul)
open ComplexWeightedKernelReflection (pairReflectionFactor differentiable_pairReflectionFactor)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary weightedDual)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun m => Langlands.GeneralLinear m ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "N" => fun m => Langlands.GeneralLinear.upperUnipotent m ℂ
local notation "KU" => fun m => unitaryCompact ℂ m
local notation "M" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "SD" => complexSelfDualMeasure
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "δg" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "Rank" => t + 1 + q + 1
local notation "LowerIndex" => t + 1 + q
local notation "Tail" => N (q + 1)
local notation "H" => G (t + 1)
local notation "P" => RetainedPoint t q
local notation "ν" => complexGeneralLinearHaar Small

local notation "ι" => inverseTranspose Small ℂ
local notation "Side" => Outer Small q × Tail
local notation "Ord" => Q t × Side
local notation "X₀" => Q t × M (LowerIndex - Small) Small
local notation "X₁" => Q t × M q Small
local notation "Dual" => Q t × (Outer Small q × (M q Small × Tail))

/-- The compact Haar measure in the upper group, using the chart's subtype measurable structure. -/
def retainedCompactHaar : Measure (KU Rank) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (KU Rank))

local notation "κ" => retainedCompactHaar t q

instance : (κ).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
instance : IsProbabilityMeasure κ := isProbabilityMeasure_haarMeasure_top

/-- The retained part of the separated Haar measure. -/
def retainedHaar (a : ℂˣ) : Measure P :=
  (retainedMeasure Small q (SD a) κ).prod (entryHaar (SD a) (q + 1))

instance (a : ℂˣ) : SigmaFinite (retainedHaar t q a) := by
  let : SigmaFinite (entryHaar (SD a) (q + 1)) := entryHaar_sigmaFinite _ _
  let : SigmaFinite (retainedMeasure Small q (SD a) κ) := sigmaFinite_retainedMeasure _ _ _ _
  unfold retainedHaar
  infer_instance

private def splitSide : Side ≃ᵐ H × P :=
  (MeasurableEquiv.prodCongr (splitOuter Small q) (MeasurableEquiv.refl Tail)).trans MeasurableEquiv.prodAssoc

private theorem splitSide_preserving (a : ℂˣ) :
    MeasurePreserving (splitSide t q) (ordinaryChartMeasure t q a κ) ((ν).prod (retainedHaar t q a)) := by
  let η := entryHaar (SD a) (q + 1)
  let τ := retainedMeasure Small q (SD a) κ
  let : SigmaFinite η := entryHaar_sigmaFinite _ _
  let : (SD a).measure.IsAddHaarMeasure := (SD a).isAddHaar
  let : SigmaFinite (ComplexGapTriangularChart.outerMeasure Small q (SD a) κ) := by
    unfold ComplexGapTriangularChart.outerMeasure
    infer_instance
  let : SigmaFinite (ComplexGapUnitDeterminant.unitOuterMeasure Small q (SD a) κ) := SigmaFinite.withDensity _
  let : SigmaFinite τ := sigmaFinite_retainedMeasure _ _ _ _
  exact (measurePreserving_prodAssoc ν τ η).comp
    ((complexGapLeadingHaar Small q (SD a) κ inferInstance).prod (MeasurePreserving.id η))

private def splitChart (A : Type*) [MeasurableSpace A] : A × Side ≃ᵐ P × (A × H) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) (splitSide t q)).trans
    (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm)

private theorem splitChart_preserving (a : ℂˣ) {A : Type*} [MeasurableSpace A] (μ : Measure A) [SFinite μ] :
    MeasurePreserving (splitChart t q A) (μ.prod (ordinaryChartMeasure t q a κ))
      ((retainedHaar t q a).prod (μ.prod ν)) := by
  let : SigmaFinite (ordinaryChartMeasure t q a κ) := sigmaFinite_ordinaryChartMeasure t q a κ
  exact measurePreserving_swap.comp (((measurePreserving_prodAssoc μ ν (retainedHaar t q a)).symm _).comp
    ((MeasurePreserving.id μ).prod (splitSide_preserving t q a)))

private def lowerChart : Dual ≃ᵐ X₀ × Side :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t)) interchangeFirst).trans
    (MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t)) (rectangleRows t q).symm) (MeasurableEquiv.refl Side)))

private theorem lowerChart_preserving (a : ℂˣ) (D : ComplexQuotientMeasureData t) :
    MeasurePreserving (lowerChart t q) (D.measure.prod (dualChartMeasure t q a κ))
      ((complexUnequalDualMeasure (r := LowerIndex) (-a) D).prod (ordinaryChartMeasure t q a κ)) := by
  let σ := ComplexGapUnitDeterminant.unitOuterMeasure Small q (SD a) κ
  let η := entryHaar (SD a) (q + 1)
  let ξ := rectangularMeasure (SD a) q Small
  let ξ₀ := rectangularMeasure (SD a) (LowerIndex - Small) Small
  let : (SD a).measure.IsAddHaarMeasure := (SD a).isAddHaar
  let : SigmaFinite (SD a).measure := inferInstance
  let : SigmaFinite (ComplexGapTriangularChart.outerMeasure Small q (SD a) κ) := by
    unfold ComplexGapTriangularChart.outerMeasure
    infer_instance
  let : SigmaFinite σ := SigmaFinite.withDensity _
  let : SigmaFinite η := entryHaar_sigmaFinite _ _
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : ξ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : ξ₀.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ξ := inferInstance
  let : SigmaFinite ξ₀ := inferInstance
  have hμ : complexUnequalDualMeasure (r := LowerIndex) (-a) D = D.measure.prod ξ₀ := by
    unfold complexUnequalDualMeasure
    rw [Langlands.GodementJacquet.complexSelfDualMeasure_neg_scale]
  rw [hμ]
  have h₁ := (MeasurePreserving.id D.measure).prod (measurePreserving_interchangeFirst σ ξ η)
  have h₂ := (measurePreserving_prodAssoc D.measure ξ (σ.prod η)).symm _
  have h₃ := ((MeasurePreserving.id D.measure).prod
    ((measurePreserving_rectangleRows t q (SD a)).symm _)).prod (MeasurePreserving.id (σ.prod η))
  exact h₃.comp (h₂.comp h₁)

private def ordinaryReindex : P × (Q t × H) ≃ᵐ Ord := (splitChart t q (Q t)).symm

private def reflectedReindex : P × (X₀ × H) ≃ᵐ Dual :=
  ((lowerChart t q).trans (splitChart t q X₀)).symm

private theorem ordinaryReindex_apply (p : P × (Q t × H)) :
    ordinaryReindex t q p = (p.2.1, outerWithLeading Small q p.2.2 p.1.1, p.1.2) := rfl

private theorem reflectedReindex_apply (p : P × (X₀ × H)) :
    reflectedReindex t q p = (p.2.1.1, outerWithLeading Small q p.2.2 p.1.1, rectangleRows t q p.2.1.2, p.1.2) := rfl

private theorem square_spectral (d : ComplexCharacterData) (Φ : M Small Small → ℂ) (s : ℂ) (z : H) :
    squareKernel d Φ (fun _ => 1) s z = squareKernel d Φ (fun _ => 1) 0 z * (δg z : ℂ) ^ s := by
  let σ := (t : ℂ) / 2
  have hχ : characterWeight d (σ + s) (determinant z) = characterWeight d σ (determinant z) * (δg z : ℂ) ^ s := by
    change (d.character (determinant z) : ℂ) * normPower (σ + s) (determinant z) =
      (d.character (determinant z) : ℂ) * normPower σ (determinant z) * (δg z : ℂ) ^ s
    have hp : (δg z : ℂ) ^ s = ArchimedeanLocal.detPower complexNormalizedAbs z s := normPower_determinant z s
    rw [normPower_determinant, normPower_determinant, detPower_add, hp, mul_assoc]
  unfold squareKernel
  rw [add_zero, hχ]
  ring

private theorem ordinaryFiber_reindex (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors Small q)
    (W : G Rank → ℂ) (V : H → ℂ) (s : ℂ) (p : P × (Q t × H)) :
    let F := ordinarySeparatedKernel t q false a d T W V (fun _ => 1) (fun _ => 1)
    let C := retainedGroup t q p.1
    F (ordinaryReindex t q p) * (ordinaryProductDet t q (ordinaryReindex t q p) : ℂ) ^ s =
      retainedCoefficient t q a d T C * ordinaryFiber (rankLT t q) d (leadingSquareTest t q C T.leading) (ρ C⁻¹ W) V s p.2 := by
  intro F C
  dsimp only [F]
  rw [ordinaryReindex_apply]
  simp only [ordinarySeparatedKernel, ordinaryProductDet, weightedOrdinary, retainedTail_outerWithLeading,
    leadingSide, Bool.false_eq_true, ↓reduceIte, squareLeading, mul_one]
  let A := retainedCoefficient t q a d T C
  let Ψ := leadingSquareTest t q C T.leading
  let U := ρ C⁻¹ W
  change A * complexUnequalIntegrand (rankLT t q) U (ρ p.2.2 V) 0 p.2.1 *
    squareKernel d Ψ (fun _ => 1) 0 p.2.2 * ((quotientDetAbs p.2.1 * δg p.2.2 : ℝ) : ℂ) ^ s = _
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (quotientDetAbs_pos p.2.1).le
    (Langlands.GodementJacquet.complexNormalizedAbs_det_pos p.2.2).le, ordinaryFiber]
  change _ = A * (complexUnequalIntegrand (rankLT t q) U (ρ p.2.2 V) s p.2.1 *
    squareKernel d Ψ (fun _ => 1) s p.2.2)
  rw [complexUnequalIntegrand_eq_mul (rankLT t q) U (ρ p.2.2 V) s, square_spectral t d Ψ s]
  ring

private theorem reflectedFiber_reindex (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors Small q)
    (W : G Rank → ℂ) (V : H → ℂ) (s : ℂ) (p : P × (X₀ × H)) :
    let F := dualSeparatedKernel t q a d T W V (fun _ => 1) (fun _ => 1)
    let C := retainedGroup t q p.1
    let S := (d.inv.character (determinant (weylLong (q + 1) ℂ)) : ℂ)
    F (reflectedReindex t q p) * (dualProductDet t q (reflectedReindex t q p) : ℂ) ^ s =
      (S * retainedCoefficient t q a d T C) * reflectedFiber (rankLT t q) a d (leadingSquareTest t q C T.leading) (ρ C⁻¹ W) V s p.2 := by
  intro F C S
  dsimp only [F]
  rw [reflectedReindex_apply]
  simp only [dualSeparatedKernel, dualProductDet, dualLeadingDet, weightedDual, mul_one,
    MeasurableEquiv.symm_apply_apply, retainedTail_outerWithLeading]
  let A := retainedCoefficient t q a d T C
  let Ψ := splitSquareTransform a (leadingSquareTest t q C T.leading)
  let U := ρ C⁻¹ W
  change S * A * complexUnequalDualKernel (rankLT t q) U (ρ p.2.2 V) 0 p.2.1 *
    squareKernel d.inv Ψ (fun _ => 1) 0 (ι p.2.2) * ((quotientDetAbs p.2.1.1 * δg (ι p.2.2) : ℝ) : ℂ) ^ s = _
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (quotientDetAbs_pos p.2.1.1).le
    (Langlands.GodementJacquet.complexNormalizedAbs_det_pos (ι p.2.2)).le, reflectedFiber]
  change _ = S * A * (complexUnequalDualKernel (rankLT t q) U (ρ p.2.2 V) s p.2.1 *
    squareKernel d.inv Ψ (fun _ => 1) s (ι p.2.2))
  rw [complexUnequalDualKernel_eq_mul (rankLT t q) U (ρ p.2.2 V) s, square_spectral t d.inv Ψ s]
  ring

private theorem continuous_retainedCoefficient (a : ℂˣ) (d : ComplexCharacterData)
    (T : GodementColumnFactors Small q) :
    Continuous (fun p : P => retainedCoefficient t q a d T (retainedGroup t q p)) := by
  have hCol (j : Fin (q + 1)) : Continuous (fun x : G Rank => tailColumn Small q x j) := by
    unfold tailColumn
    fun_prop
  have hTail : Continuous (tailFactor Small q a T) := by
    unfold tailFactor
    refine ((T.tail _).continuous.comp (hCol 0)).mul (continuous_finsetProd _ fun j _ => ?_)
    simp_rw [← columnTransform_apply]
    exact (columnTransform a (T.tail _)).continuous.comp ((hCol j).comp (continuous_inverseTranspose Rank ℂ))
  exact (hTail.mul ((Units.continuous_val.comp d.character.continuous).comp determinantContinuous.continuous)).comp
    (continuous_retainedGroup t q)

/-- Integration over the retained Haar coordinates identifies the entire ordinary normalization.
The positive Haar scalar is independent of the leading and tail tests. -/
def ComplexGapRetainedMellinStatement : Prop :=
  ∀ a : ℂˣ, ∃ c : ℝ≥0, 0 < c ∧
    ∀ (D : ComplexQuotientMeasureData t) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    ds.length = Rank → es.length = Small →
    ∀ (W : complexWhittakerModel LowerIndex ds (-a)) (V : complexWhittakerModel t es a)
      (T : GodementColumnFactors Small q) (Φ : EntrySchwartz Rank (Rank + 1)), (∀ X, Φ X = T.eval Small q X) →
    ∀ J : P → ℂ → ℂ, (∀ s, Continuous (fun p => J p s)) →
    (∀ p, Differentiable ℂ (J p) ∧ HasStripExponentialGrowth (J p)) →
    let χ (p : P) := leadingSquareTest t q (retainedGroup t q p) T.leading
    let U (p : P) := ρ (retainedGroup t q p)⁻¹ W.val
    let E (s : ℂ) := pairReflectionFactor ds es (-a) (complexCentralSign es ^ LowerIndex) s *
      pairReflectionFactor [d] es a 1 s
    let L := (complexPairLFactor (d :: ds) es).denominator
    let Ld := (complexPairLFactor ((d :: ds).map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
    let μ := D.measure.prod ν
    let μd := (complexUnequalDualMeasure (r := LowerIndex) (-a) D).prod ν
    (∀ p, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      (Integrable (ordinaryFiber (rankLT t q) d (χ p) (U p) V.val s) μ →
        L s * (∫ x, ordinaryFiber (rankLT t q) d (χ p) (U p) V.val s x ∂μ) = J p s) ∧
      (Integrable (reflectedFiber (rankLT t q) a d (χ p) (U p) V.val s) μd →
        Ld s * (∫ x, reflectedFiber (rankLT t q) a d (χ p) (U p) V.val s x ∂μd) = E (1 - s) * J p (1 - s))) →
    let F (s : ℂ) (p : P) := retainedCoefficient t q a d T (retainedGroup t q p) * J p s
    let integrated (s : ℂ) := ∫ p, F s p ∂retainedHaar t q a
    (∀ s, Integrable (F s) (retainedHaar t q a)) ∧ Differentiable ℂ integrated ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        L s * complexUnequalIntegral (rankLT t (q + 1)) D (rotatedValue t q a d Φ W.val 0) V.val s =
          (ordinaryWeylPhase t q d * (c : ℂ)) * integrated s

set_option maxHeartbeats 2100000 in
theorem complexGapRetainedMellin : ComplexGapRetainedMellinStatement t q := by
  intro a
  let hκ : (κ).IsHaarMeasure := inferInstance
  have hκi : (κ).IsInvInvariant := isInvInvariant_of_compact κ
  obtain ⟨c, hc, hExact⟩ := complexGapExactRestriction t q a κ hκ hκi
  refine ⟨c, hc, ?_⟩
  intro D d ds es hds hes W V T Φ hΦ J hJc hJ χ U E L Ld μ μd hEnd F integrated
  let η := retainedHaar t q a
  let m := D.measure.prod (ordinaryChartMeasure t q a κ)
  let md := D.measure.prod (dualChartMeasure t q a κ)
  let U₀ := rotatedValue t q a d Φ W.val 0
  let G₀ := ordinarySeparatedKernel t q false a d T W.val V.val (fun _ => 1) (fun _ => 1)
  let Gd := dualSeparatedKernel t q a d T W.val V.val (fun _ => 1) (fun _ => 1)
  obtain ⟨hOm, b₁, hO⟩ := complexGapOrdinaryMellin t q D a κ hκ c d T Φ ds es W V
    (fun g => (hExact ds hds d Φ T hΦ W g 0).1.2)
  obtain ⟨hRm, b₂, hR⟩ := complexGapDualMellin t q D a κ hκ hκi c d T Φ hΦ ds es hds hes W V U₀
    (fun g y => ((hExact ds hds d Φ T hΦ W g 0).2 y).2)
  let μ₀ := complexUnequalDualMeasure (r := LowerIndex) (-a) D
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : (rectangularMeasure (SD (-a)) (LowerIndex - Small) Small).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite μ₀ := by unfold μ₀ complexUnequalDualMeasure; infer_instance
  let : SigmaFinite μ := by dsimp only [μ]; infer_instance
  let : SigmaFinite μd := by change SigmaFinite (μ₀.prod ν); infer_instance
  let eo := ordinaryReindex t q
  let er := reflectedReindex t q
  have heo : MeasurePreserving eo (η.prod μ) m := (splitChart_preserving t q a D.measure).symm _
  have her : MeasurePreserving er (η.prod μd) md :=
    ((splitChart_preserving t q a μ₀).comp (lowerChart_preserving t q a D)).symm _
  let O := G₀ ∘ eo
  let R := Gd ∘ er
  let δ := ordinaryProductDet t q ∘ eo
  let δd := dualProductDet t q ∘ er
  let b := max b₁ b₂
  have hIo (x : ℝ) (hx : b ≤ x) : Integrable (fun p => ‖O p‖ * δ p ^ x) (η.prod μ) := by
    have hs := hO (x : ℂ) (by simpa only [Complex.ofReal_re] using (le_max_left b₁ b₂).trans hx)
    change Integrable ((fun p => ‖G₀ p‖ * ordinaryProductDet t q p ^ x) ∘ eo) (η.prod μ)
    simpa only [Complex.ofReal_re] using heo.integrable_comp_of_integrable hs.1
  have hIr (x : ℝ) (hx : b ≤ x) : Integrable (fun p => ‖R p‖ * δd p ^ x) (η.prod μd) := by
    have hs := hR (x : ℂ) (by simpa only [Complex.ofReal_re] using (le_max_right b₁ b₂).trans hx)
    change Integrable ((fun p => ‖Gd p‖ * dualProductDet t q p ^ x) ∘ er) (η.prod μd)
    simpa only [Complex.ofReal_re] using her.integrable_comp_of_integrable hs.1
  let S := (d.inv.character (determinant (weylLong (q + 1) ℂ)) : ℂ)
  have hS : S ≠ 0 := Units.ne_zero _
  have hZ : complexCentralSign es ^ LowerIndex ≠ 0 := pow_ne_zero _ (fun h => by
    have h₀ := complexCentralSign_sq es
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h₀
    exact zero_ne_one h₀)
  have hE (s : ℂ) : E s ≠ 0 := mul_ne_zero (mul_ne_zero hZ (Units.ne_zero _)) (mul_ne_zero one_ne_zero (Units.ne_zero _))
  let Rd (s : ℂ) := (S * E (1 - s))⁻¹ * Ld s
  have hEd : Differentiable ℂ E := (differentiable_pairReflectionFactor _ _ _ _).mul
    (differentiable_pairReflectionFactor _ _ _ _)
  have hRd : Differentiable ℂ Rd := (((hEd.comp (differentiable_id.const_sub 1)).const_mul S).inv
    (fun s => mul_ne_zero hS (hE _))).mul (complexPairLFactor _ _).entire
  have hRi : StripExpType (fun s => (E s)⁻¹) :=
    ((stripExpType_pairReflectionFactor_inv ds es (-a) (complexCentralSign es ^ LowerIndex)).mul
      (stripExpType_pairReflectionFactor_inv [d] es a 1)).congr (fun s => (mul_inv _ _).symm)
  have hRs : StripExpType Rd := by
    have h := (hRi.comp_ofReal_mul (-1)).comp_add (-1)
    have hLd : StripExpType Ld := complexLFactor_stripExpType
      (complexPairBlocks ((d :: ds).map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv))
    refine (((StripExpType.const S⁻¹).mul h).mul hLd).congr (fun s => ?_)
    have he : ((-1 : ℝ) : ℂ) * (s + -1) = 1 - s := by push_cast; ring
    simp only [he, Rd, mul_inv]
  let γ (p : P) := retainedCoefficient t q a d T (retainedGroup t q p)
  have hFc (s : ℂ) : AEStronglyMeasurable (fun p => F s p) η :=
    ((continuous_retainedCoefficient t q a d T).mul (hJc s)).aestronglyMeasurable
  have hF (p : P) : Differentiable ℂ (fun s => F s p) ∧ HasStripExponentialGrowth (fun s => F s p) :=
    ⟨(hJ p).1.const_mul _, (hJ p).2.const_mul _⟩
  have hEndpoints (p : P) : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      (Integrable (fun x => O (p, x) * (δ (p, x) : ℂ) ^ s) μ →
        L s * (∫ x, O (p, x) * (δ (p, x) : ℂ) ^ s ∂μ) = F s p) ∧
      (Integrable (fun x => R (p, x) * (δd (p, x) : ℂ) ^ s) μd →
        Rd s * (∫ x, R (p, x) * (δd (p, x) : ℂ) ^ s ∂μd) = F (1 - s) p) := by
    obtain ⟨b, hb⟩ := hEnd p
    refine ⟨b, fun s hs => ?_⟩
    let K := ordinaryFiber (rankLT t q) d (χ p) (U p) V.val s
    let Kd := reflectedFiber (rankLT t q) a d (χ p) (U p) V.val s
    have heo (x : Q t × H) : O (p, x) * (δ (p, x) : ℂ) ^ s = γ p * K x :=
      ordinaryFiber_reindex t q a d T W.val V.val s (p, x)
    have her (x : X₀ × H) : R (p, x) * (δd (p, x) : ℂ) ^ s = (S * γ p) * Kd x :=
      reflectedFiber_reindex t q a d T W.val V.val s (p, x)
    constructor
    · simp_rw [heo, integral_const_mul]
      intro hi
      by_cases hγ : γ p = 0
      · change L s * (γ p * (∫ x, K x ∂μ)) = γ p * J p s
        simp only [hγ, zero_mul, mul_zero]
      · have hK : Integrable K μ := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hγ) K).mp hi
        change L s * (γ p * (∫ x, K x ∂μ)) = γ p * J p s
        rw [mul_left_comm, (hb s hs).1 hK]
    · simp_rw [her, integral_const_mul]
      intro hi
      by_cases hγ : γ p = 0
      · change Rd s * ((S * γ p) * (∫ x, Kd x ∂μd)) = γ p * J p (1 - s)
        simp only [hγ, mul_zero, zero_mul]
      · have hKd : Integrable Kd μd :=
          (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (mul_ne_zero hS hγ)) Kd).mp hi
        change ((S * E (1 - s))⁻¹ * Ld s) * ((S * γ p) * (∫ x, Kd x ∂μd)) = γ p * J p (1 - s)
        calc
          _ = ((S * E (1 - s))⁻¹ * (S * γ p)) * (Ld s * ∫ x, Kd x ∂μd) := by ring
          _ = _ := by
            rw [(hb s hs).2 hKd]
            field_simp [hS, hE]
  obtain ⟨hNi, hNd, hNr⟩ := archimedeanMellinMarginal η μ μd O R δ δd
    (hOm.comp_quasiMeasurePreserving heo.quasiMeasurePreserving) (hRm.comp_quasiMeasurePreserving her.quasiMeasurePreserving)
    ((measurable_ordinaryProductDet t q).comp eo.measurable) ((measurable_dualProductDet t q).comp er.measurable)
    (fun p => ordinaryProductDet_pos t q (eo p)) (fun p => dualProductDet_pos t q (er p))
    b hIo hIr L Rd (complexPairLFactor _ _).entire hRd (complexLFactor_stripExpType _) hRs
    (fun p s => F s p) hFc (ae_of_all _ hF) (ae_of_all _ hEndpoints)
  refine ⟨hNi, hNd, b, fun s hs => ?_⟩
  have he := heo.integral_comp eo.measurableEmbedding (fun p => G₀ p * (ordinaryProductDet t q p : ℂ) ^ s)
  have hZ := (hO s ((le_max_left b₁ b₂).trans hs.le)).2
  rw [hZ]
  change L s * ((ordinaryWeylPhase t q d * (c : ℂ)) *
    (∫ p, G₀ p * (ordinaryProductDet t q p : ℂ) ^ s ∂m)) = _
  rw [mul_left_comm, ← he]
  exact congrArg (fun z => ordinaryWeylPhase t q d * (c : ℂ) * z) (hNr s hs).symm

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained
