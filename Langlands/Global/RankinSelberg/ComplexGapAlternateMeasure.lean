import Langlands.Global.RankinSelberg.ComplexGapSplitNormConvergence
import Langlands.Global.RankinSelberg.ComplexGapAlternateCoordinates

/-! # Product measure transport for the alternate complex chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateMeasure

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (ComplexQuotientMeasureData)
open ComplexGapSplitNormConvergence (alternateGapProductMeasure)
open ComplexGapAlternateCoordinates (logCongr unipotentCongr)
open ComplexGapAlternateTailConvergence (alternateTailProductMeasure)
open ComplexGapRightChart (consecutiveTailWeight measurable_consecutiveTailWeight tailSize)
open ComplexGapTailIwasawa (tailModulus measurable_tailModulus tailDiagonalMeasure)
open ComplexGapTriangularChart (Outer outerMeasure diagonalWeightMeasure)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexLocalIwasawa (continuous_logTorus)
open ComplexLocalWhittakerGauge (logTorus)

private theorem measurePreserving_reorder
    {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]
    (ma : Measure A) (mb : Measure B) (mc : Measure C) (md : Measure D) (me : Measure E) (mf : Measure F)
    [SFinite ma] [SFinite mb] [SFinite mc] [SFinite md] [SFinite me] [SFinite mf] :
    MeasurePreserving
      (fun p : (A × (B × (C × (D × E)))) × F =>
        (((((p.2, p.1.2.1), p.1.2.2.2.2), p.1.2.2.2.1), p.1.2.2.1), p.1.1))
      ((ma.prod (mb.prod (mc.prod (md.prod me)))).prod mf)
      (((((mf.prod mb).prod me).prod md).prod mc).prod ma) := by
  let ν := mb.prod (mc.prod (md.prod me))
  let νFE := mf.prod mb
  have h₁ := measurePreserving_swap (μ := ma.prod ν) (ν := mf)
  have h₂ := (MeasurePreserving.id mf).prod (measurePreserving_swap (μ := ma) (ν := ν))
  have h₃ := (measurePreserving_prodAssoc mf ν ma).symm MeasurableEquiv.prodAssoc
  have h₄ := (measurePreserving_prodAssoc mf mb (mc.prod (md.prod me))).symm MeasurableEquiv.prodAssoc
  have h₅ := measurePreserving_swap (μ := mc) (ν := md.prod me)
  have h₆ := (measurePreserving_swap (μ := md) (ν := me)).prod (MeasurePreserving.id mc)
  have h₇ := (MeasurePreserving.id νFE).prod (h₆.comp h₅)
  have h₈ := (measurePreserving_prodAssoc νFE (me.prod md) mc).symm MeasurableEquiv.prodAssoc
  have h₉ := ((measurePreserving_prodAssoc νFE me md).symm MeasurableEquiv.prodAssoc).prod
    (MeasurePreserving.id mc)
  exact ((h₉.comp (h₈.comp (h₇.comp h₄))).prod (MeasurePreserving.id ma)).comp
    (h₃.comp (h₂.comp h₁))

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "K" => fun n => unitaryCompact ℂ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ

attribute [local instance] ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel
local instance gapMeasureNMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance gapMeasureNBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩
local instance gapMeasureGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapMeasureGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

private theorem measurePreserving_logCongr {m n : ℕ} (h : m = n) :
    MeasurePreserving (logCongr h) volume volume := by
  subst n
  exact MeasurePreserving.id _

private theorem measurePreserving_unipotentCongr {m n : ℕ} (h : m = n) (μ : AdditiveHaarMeasure ℂ) :
    MeasurePreserving (unipotentCongr h) (entryHaar μ m) (entryHaar μ n) := by
  subst n
  exact MeasurePreserving.id _

variable (t q : ℕ)

local notation "Small" => (t + 1)
local notation "Order" => (t + 1 + q)
local notation "Size" => (t + 1 + q + 1)
local notation "d" => (t + 1 + q + 1 - (t + 1))
local notation "e" => (tailSize Small q)
local notation "Z" => Outer Small q × N (q + 1)
local notation "Coords" => (Q t × ((Fin d → ℝ) × (N d × ((Fin Small → ℂ) × K Size)))) ×
  (G Small × M d Small)

/-- Recover the consecutive chart from the absolute estimates' product.
Negation accounts for the sign in the logarithmic tail coordinates. -/
def alternateToConsecutive (p : Coords) : Z × Q t :=
  (((((p.2.1, logCongr (e).symm (-p.1.2.1)), p.1.2.2.2.2), p.1.2.2.2.1),
    unipotentCongr (e).symm p.1.2.2.1), p.1.1)

/-- The chart with unweighted Lebesgue measure in the logarithmic tail. -/
def consecutiveUnweightedMeasure (D : ComplexQuotientMeasureData t)
    (μ : AdditiveHaarMeasure ℂ) (κ : Measure (K Size)) : Measure (Z × Q t) :=
  (((((complexGeneralLinearHaar Small).prod volume).prod κ).prod (rowMeasure μ Small)).prod
    (entryHaar μ (q + 1))).prod D.measure

/-- The product of the root modulus and right-tail determinant weight on the consecutive chart. -/
def consecutiveDensity (p : Z × Q t) : ℝ≥0 :=
  let y := p.1.1.1.1.2
  tailModulus y * consecutiveTailWeight Small q (logTorus y)

private theorem measurable_logDensity :
    Measurable (fun y : Fin (q + 1) → ℝ =>
      ((tailModulus y * consecutiveTailWeight Small q (logTorus y) : ℝ≥0) : ℝ≥0∞)) := by
  simp only [ENNReal.coe_mul]
  exact measurable_tailModulus.mul ((measurable_consecutiveTailWeight Small q).comp
    continuous_logTorus.measurable)

/-- The transported density is measurable on the whole consecutive chart. -/
theorem measurable_consecutiveDensity :
    Measurable (fun p : Z × Q t => (consecutiveDensity t q p : ℝ≥0∞)) :=
  (measurable_logDensity t q).comp
    (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
      (measurable_fst.comp measurable_fst))))

/-- The absolute estimates' product measure maps to the unweighted chart.
The actual alternate chart is obtained by reinserting the two tail densities. -/
def ComplexGapAlternateMeasureStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (μ : AdditiveHaarMeasure ℂ) (κ : Measure (K Size)),
    κ.IsHaarMeasure → ∀ (νY : Measure (M d Small)) [IsProbabilityMeasure νY],
    MeasurePreserving (alternateToConsecutive t q) (alternateGapProductMeasure Order t D μ κ νY)
      (consecutiveUnweightedMeasure t q D μ κ) ∧
    (((outerMeasure Small q μ κ).prod (entryHaar μ (q + 1))).prod D.measure) =
      (consecutiveUnweightedMeasure t q D μ κ).withDensity (fun p => (consecutiveDensity t q p : ℝ≥0∞))

set_option maxHeartbeats 950000 in
theorem complexGapAlternateMeasure : ComplexGapAlternateMeasureStatement t q := by
  intro D μ κ hκ νY _
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace (K Size) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : SigmaFinite (entryHaar μ d) := entryHaar_sigmaFinite μ _
  let : SigmaFinite (entryHaar μ (q + 1)) := entryHaar_sigmaFinite μ _
  let ρ := rowMeasure μ Small
  let σ := complexGeneralLinearHaar Small
  let ν := D.measure
  let θ := alternateTailProductMeasure Order t D μ κ
  let : SFinite θ := by unfold θ alternateTailProductMeasure; infer_instance
  have hLog := measurePreserving_logCongr (e).symm
  have hNeg := Measure.measurePreserving_neg (volume : Measure (Fin d → ℝ))
  have hEntry := measurePreserving_unipotentCongr (e).symm μ
  have hCast := ((MeasurePreserving.id ν).prod ((hLog.comp hNeg).prod
    (hEntry.prod (MeasurePreserving.id (ρ.prod κ))))).prod (MeasurePreserving.id σ)
  have hDrop : MeasurePreserving Prod.fst (σ.prod νY) σ := measurePreserving_fst
  have hChart := measurePreserving_reorder ν (volume : Measure (Fin (q + 1) → ℝ))
    (entryHaar μ (q + 1)) ρ κ σ
  refine ⟨hChart.comp (hCast.comp ((MeasurePreserving.id θ).prod hDrop)), ?_⟩
  let f (y : Fin (q + 1) → ℝ) : ℝ≥0∞ :=
    ((tailModulus y * consecutiveTailWeight Small q (logTorus y) : ℝ≥0) : ℝ≥0∞)
  have hf : Measurable f := measurable_logDensity t q
  have hDiag : diagonalWeightMeasure Small q = volume.withDensity f := by
    unfold diagonalWeightMeasure tailDiagonalMeasure f
    simp only [ENNReal.coe_mul]
    exact (withDensity_mul volume measurable_tailModulus
      ((measurable_consecutiveTailWeight Small q).comp continuous_logTorus.measurable)).symm
  let B := G Small × (Fin (q + 1) → ℝ)
  have h₀ : Measurable (fun p : B => f p.2) := hf.comp measurable_snd
  have h₁ : Measurable (fun p : B × K Size => f p.1.2) := h₀.comp measurable_fst
  have h₂ : Measurable (fun p : (B × K Size) × (Fin Small → ℂ) => f p.1.1.2) :=
    h₁.comp measurable_fst
  have h₃ : Measurable (fun p : Z => f p.1.1.1.2) := h₂.comp measurable_fst
  unfold consecutiveUnweightedMeasure outerMeasure
  rw [hDiag, prod_withDensity_right hf, prod_withDensity_left h₀, prod_withDensity_left h₁,
    prod_withDensity_left h₂, prod_withDensity_left h₃]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateMeasure
