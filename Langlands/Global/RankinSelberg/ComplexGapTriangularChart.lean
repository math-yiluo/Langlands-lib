import Langlands.Global.RankinSelberg.ComplexGapRightChart
import Langlands.Global.RankinSelberg.ComplexGapTailIwasawa
import Langlands.Representation.Archimedean.ComplexBlockModulusBound

/-! # Haar integration in the triangular split chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapTriangularChart

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC_det_unitary det_upperUnipotent)
open Langlands.GeneralLinear (blockSum blockSumContinuous rankInclusion)
open Langlands.GodementJacquet (complexAbsHom coe_complexAbsHom)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (rectangularMeasure)
open ComplexGapRightChart
open ComplexGapRectangleShear (splitTailRectangle splitTailRectangle_apply complexGapRectangleShear)
open ComplexGapTailIwasawa (tailChart tailDiagonalMeasure continuous_tailChart complexGapTailIwasawa)
open ComplexGapUpperTail
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexLocalIwasawa (continuous_logTorus)
open ComplexLocalWhittakerGauge (logTorus)

local notation "G" => fun Size => Langlands.GeneralLinear Size ℂ
local notation "Compact" => fun Size => unitaryCompact ℂ Size

local instance gapTriangularGLMeasurable (Size : ℕ) : MeasurableSpace (G Size) := borel _
local instance gapTriangularGLBorel (Size : ℕ) : BorelSpace (G Size) := ⟨rfl⟩
local instance gapTriangularGLSecondCountable (Size : ℕ) : SecondCountableTopology (G Size) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance gapTriangularGLLocallyCompact (Size : ℕ) : LocallyCompactSpace (G Size) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

variable (k q : ℕ)
local notation "Size" => k + q + 1
local notation "TailSize" => q + 1
local notation "N" => Langlands.GeneralLinear.upperUnipotent TailSize ℂ
local notation "Y" => Fin TailSize → ℝ
local notation "Head" => Fin k → ℂ
local notation "Tail" => Matrix (Fin k) (Fin q) ℂ
local notation "Rect" => Matrix (Fin k) (Fin TailSize) ℂ
local notation "Source" => ((G k × ((Y × N) × Compact TailSize)) × Rect) × Compact Size
local notation "Folded" => G k × ((Y × N) × (Rect × Compact Size))

local instance gapTriangularNMeasurable : MeasurableSpace N := borel _
local instance gapTriangularNBorel : BorelSpace N := ⟨rfl⟩

/-- The leading matrix, logarithmic tail, compact matrix and first rectangular column. -/
abbrev Outer := (((G k × Y) × Compact Size) × Head)

/-- The retained matrix in the split chart, before the later rectangle and unipotent tail. -/
def retainedMatrix (p : Outer k q) : G Size :=
  p.1.2.val * blockSum (1, logTorus p.1.1.2) * (packedTail k q (firstRectangle k q p.2) 1).val

/-- The full chart with independent later rectangle and tail variables. -/
def triangularRightChart (p : Outer k q × (Tail × N)) : G Size :=
  retainedMatrix k q p.1 * (packedTail k q (laterRectangle k q p.2.1) p.2.2).val *
    rankInclusion TailSize p.1.1.1.1

private theorem continuous_packedTail : Continuous (fun p : Rect × N => (packedTail k q p.1 p.2).val) := by
  apply (Units.isOpenEmbedding_val (R := Matrix (Fin Size) (Fin Size) ℂ)).isEmbedding.continuous_iff.mpr
  apply continuous_matrix
  intro i j
  change Continuous (fun p : Rect × N => (packedTail k q p.1 p.2).val.val i j)
  refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := TailSize) (fun j₀ => ?_) (fun j₁ => ?_) j
  · simp only [packedTail_top_left]
    exact continuous_const
  · simp only [packedTail_top_right]
    exact ((continuous_apply j₁).comp (continuous_apply i₀ : Continuous (fun X : Rect => X i₀))).comp
      continuous_fst
  · simp only [packedTail_bottom_left]
    exact continuous_const
  · simp only [packedTail_bottom_right]
    have hVal : Continuous (fun z : G TailSize => z.val) := Units.continuous_val
    exact ((continuous_apply j₁).comp
      (continuous_apply i₁ : Continuous (fun X : Matrix (Fin TailSize) (Fin TailSize) ℂ => X i₁))).comp
      (hVal.comp (continuous_subtype_val.comp continuous_snd))

private theorem continuous_firstRectangle : Continuous (firstRectangle k q) := by
  apply continuous_matrix
  intro i j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simpa only [firstRectangle, Fin.cons_zero] using continuous_apply i
  · simp only [firstRectangle, Fin.cons_succ]
    exact continuous_const

private theorem continuous_laterRectangle : Continuous (laterRectangle k q) := by
  apply continuous_matrix
  intro i j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp only [laterRectangle, Fin.cons_zero]
    exact continuous_const
  · simp only [laterRectangle, Fin.cons_succ]
    exact (continuous_apply j').comp (continuous_apply i : Continuous (fun X : Tail => X i))

private theorem continuous_diagonalTail : Continuous (fun g : G TailSize => blockSum ((1 : G k), g)) :=
  (blockSumContinuous (R := ℂ)).continuous.comp (continuous_const.prodMk continuous_id)

private theorem continuous_rankInclusion : Continuous (rankInclusion (R := ℂ) (n := k) TailSize) :=
  (Langlands.GeneralLinear.rankInclusionContinuous (R := ℂ) (n := k) TailSize).continuous

/-- The retained matrix depends continuously on its chart coordinates. -/
theorem continuous_retainedMatrix : Continuous (retainedMatrix k q) := by
  have hk : Continuous (fun p : Outer k q => p.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hy : Continuous (fun p : Outer k q => logTorus p.1.1.2) :=
    continuous_logTorus.comp (continuous_snd.comp (continuous_fst.comp continuous_fst))
  have hx := (continuous_packedTail k q).comp
    (((continuous_firstRectangle k q).comp (continuous_snd : Continuous (fun p : Outer k q => p.2))).prodMk
      (continuous_const : Continuous (fun _ : Outer k q => (1 : N))))
  exact (hk.mul ((continuous_diagonalTail k q).comp hy)).mul hx

theorem continuous_triangularRightChart : Continuous (triangularRightChart k q) := by
  have hLater : Continuous (fun p : Outer k q × (Tail × N) => laterRectangle k q p.2.1) :=
    (continuous_laterRectangle k q).comp (continuous_fst.comp continuous_snd)
  have hZ : Continuous (fun p : Outer k q × (Tail × N) => p.2.2) := continuous_snd.comp continuous_snd
  have hLead : Continuous (fun p : Outer k q × (Tail × N) => p.1.1.1.1) :=
    continuous_fst.comp (continuous_fst.comp (continuous_fst.comp continuous_fst))
  exact (((continuous_retainedMatrix k q).comp continuous_fst).mul
    ((continuous_packedTail k q).comp (hLater.prodMk hZ))).mul ((continuous_rankInclusion k q).comp hLead)

private def embeddedCompact (u : Compact TailSize) : Compact Size :=
  ⟨blockSum (n := k) (m := TailSize) ((1 : G k), u.val), by
    have he : blockSum ((1 : G k), u.val) = Langlands.Archimedean.ComplexBlockParabolic.blockDiagGL 1 u.val := by
      apply Units.ext
      rw [Langlands.Archimedean.ComplexBlockLimit.blockDiagGL_val]
      rfl
    rw [he]
    exact Langlands.Archimedean.ComplexBlockParabolicProof.blockDiagGL_mem_unitaryCompact'
      (Subgroup.one_mem _) u.2⟩

private theorem continuous_embeddedCompact : Continuous (embeddedCompact k q) :=
  ((continuous_diagonalTail k q).comp continuous_subtype_val).subtype_mk _

private def tailCompactMeasure : Measure (Compact TailSize) := Measure.haarMeasure ⊤

private instance : IsProbabilityMeasure (tailCompactMeasure q) := by
  constructor
  rw [tailCompactMeasure, ← TopologicalSpace.PositiveCompacts.coe_top]
  exact Measure.haarMeasure_self

private instance : (tailCompactMeasure q).IsHaarMeasure := by
  unfold tailCompactMeasure
  infer_instance

private theorem measurePreserving_absorbCompact (κ : Measure (Compact Size)) [SFinite κ]
    [κ.IsMulRightInvariant] :
    MeasurePreserving (fun p : Compact TailSize × Compact Size => p.2 * embeddedCompact k q p.1)
      ((tailCompactMeasure q).prod κ) κ := by
  let κ₀ := tailCompactMeasure q
  have hM : Measurable (fun p : Compact TailSize × Compact Size => p.2 * embeddedCompact k q p.1) := by
    let : SecondCountableTopology (Compact TailSize) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    let : SecondCountableTopology (Compact Size) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    exact (continuous_snd.mul ((continuous_embeddedCompact k q).comp continuous_fst)).measurable
  have h := (MeasurePreserving.id κ₀).skew_product (g := fun (u : Compact TailSize) (v : Compact Size) => v * embeddedCompact k q u)
    hM (ae_of_all _ fun u => map_mul_right_eq_self κ (embeddedCompact k q u))
  exact (measurePreserving_snd (μ := κ₀) (ν := κ)).comp h

private theorem measurePreserving_swap_first {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (η : Measure C) [SFinite μ] [SFinite ν] [SFinite η] :
    MeasurePreserving (fun p : A × (B × C) => (p.2.1, p.1, p.2.2))
      (μ.prod (ν.prod η)) (ν.prod (μ.prod η)) :=
  (measurePreserving_prodAssoc ν μ η).comp ((measurePreserving_swap.prod (MeasurePreserving.id η)).comp
    ((measurePreserving_prodAssoc μ ν η).symm _))

private def foldCompact (p : Source) : Folded :=
  (p.1.1.1, p.1.1.2.1, p.1.2, p.2 * embeddedCompact k q p.1.1.2.2)

private theorem measurePreserving_foldCompact (μ : AdditiveHaarMeasure ℂ) (δ : Measure Y)
    [SFinite δ] (κ : Measure (Compact Size)) [SFinite κ] [κ.IsMulRightInvariant] :
    let η := entryHaar μ TailSize
    let τ := rectangularMeasure μ k TailSize
    let ρ := complexGeneralLinearHaar k
    let κ₀ := tailCompactMeasure q
    MeasurePreserving (foldCompact k q) (((ρ.prod ((δ.prod η).prod κ₀)).prod τ).prod κ)
      (ρ.prod ((δ.prod η).prod (τ.prod κ))) := by
  intro η τ ρ κ₀
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ TailSize
  let L := δ.prod η
  let R := τ.prod κ
  let S := L.prod κ₀
  have h₁ := measurePreserving_prodAssoc (ρ.prod S) τ κ
  have h₂ := measurePreserving_prodAssoc ρ S R
  have h₃ := (MeasurePreserving.id ρ).prod (measurePreserving_prodAssoc L κ₀ R)
  have h₄ := (MeasurePreserving.id ρ).prod ((MeasurePreserving.id L).prod (measurePreserving_swap_first κ₀ τ κ))
  have h₅ := (MeasurePreserving.id ρ).prod ((MeasurePreserving.id L).prod
    ((MeasurePreserving.id τ).prod (measurePreserving_absorbCompact k q κ)))
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

private def finishSplit (p : Folded) : Outer k q × (Tail × N) :=
  let u := splitTailRectangle k q (p.2.2.1, p.2.1.2)
  ((((p.1, p.2.1.1), p.2.2.2), u.1), u.2)

private theorem measurePreserving_finishSplit (μ : AdditiveHaarMeasure ℂ) (δ : Measure Y)
    [SFinite δ] (κ : Measure (Compact Size)) [SFinite κ] :
    let η := entryHaar μ TailSize
    let τ := rectangularMeasure μ k TailSize
    let ρ := complexGeneralLinearHaar k
    MeasurePreserving (finishSplit k q) (ρ.prod ((δ.prod η).prod (τ.prod κ)))
      ((((ρ.prod δ).prod κ).prod (rowMeasure μ k)).prod ((rectangularMeasure μ k q).prod η)) := by
  intro η τ ρ
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ TailSize
  let χ := rowMeasure μ k
  let ξ := (rectangularMeasure μ k q).prod η
  have h₁ := (MeasurePreserving.id ρ).prod (measurePreserving_prodAssoc δ η (τ.prod κ))
  have h₂ := (MeasurePreserving.id ρ).prod ((MeasurePreserving.id δ).prod (measurePreserving_swap_first η τ κ))
  have h₃ := (MeasurePreserving.id ρ).prod ((MeasurePreserving.id δ).prod
    ((measurePreserving_prodAssoc τ η κ).symm _))
  have h₄ := (MeasurePreserving.id ρ).prod ((MeasurePreserving.id δ).prod
    (measurePreserving_swap (μ := τ.prod η) (ν := κ)))
  have h₅ := (MeasurePreserving.id ρ).prod ((MeasurePreserving.id δ).prod
    ((MeasurePreserving.id κ).prod (complexGapRectangleShear k q μ)))
  have h₆ := (measurePreserving_prodAssoc ρ δ (κ.prod (χ.prod ξ))).symm _
  have h₇ := (measurePreserving_prodAssoc (ρ.prod δ) κ (χ.prod ξ)).symm _
  have h₈ := (measurePreserving_prodAssoc ((ρ.prod δ).prod κ) χ ξ).symm _
  exact h₈.comp (h₇.comp (h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))))))

private def replaceTail (p : Source) : ((G k × G TailSize) × Rect) × Compact Size :=
  (((p.1.1.1, tailChart p.1.1.2), p.1.2), p.2)

private theorem chart_composition : consecutiveRightChart k q ∘ replaceTail k q =
    triangularRightChart k q ∘ finishSplit k q ∘ foldCompact k q := by
  funext p
  let Z := p.1.1.2.1.2
  let a := logTorus p.1.1.2.1.1
  let b := (p.2 * embeddedCompact k q p.1.1.2.2).val * blockSum ((1 : G k), a)
  let A := rankInclusion TailSize p.1.1.1
  have hb : blockSum ((1 : G k), (tailChart p.1.1.2)) =
      blockSum ((1 : G k), p.1.1.2.2.val) * blockSum ((1 : G k), a) * (packedTail k q 0 Z).val := by
    change blockSum ((1 : G k), p.1.1.2.2.val * a * Z.val) = _
    have hZ : blockSum ((1 : G k), Z.val) = (packedTail k q 0 Z).val := by
      apply Units.ext
      rfl
    rw [← hZ, ← map_mul, ← map_mul]
    simp only [Prod.mk_mul_mk, one_mul]
  have ht : (packedTail k q 0 Z).val * (packedTail k q p.1.2 1).val = (packedTail k q p.1.2 Z).val := by
    simpa only [Subgroup.coe_mul, Matrix.zero_mul, add_zero, mul_one] using
      congrArg Subtype.val (packedTail_mul k q 0 p.1.2 Z (1 : N))
  have hp : consecutiveRightChart k q (replaceTail k q p) = b * (packedTail k q p.1.2 Z).val * A := by
    unfold consecutiveRightChart
    change p.2.val * blockSum ((1 : G k), tailChart p.1.1.2) * (packedTail k q p.1.2 1).val * A = _
    rw [hb, ← ht]
    simp only [b, Subgroup.coe_mul, embeddedCompact, mul_assoc]
  rw [Function.comp_apply, hp]
  change b * (packedTail k q p.1.2 Z).val * A = _
  let t := splitTailRectangle k q (p.1.2, Z)
  change _ = b * (packedTail k q (firstRectangle k q t.1) 1).val *
    (packedTail k q (laterRectangle k q t.2.1) t.2.2).val * A
  have hsplit := congrArg Subtype.val (packedTail_split k q p.1.2 Z)
  rw [hsplit]
  simp only [t, splitTailRectangle_apply, Subgroup.coe_mul, mul_assoc]

/-- Logarithmic diagonal measure with the tail modulus and the consecutive Haar density. -/
def diagonalWeightMeasure : Measure Y :=
  (tailDiagonalMeasure q).withDensity (fun y => (consecutiveTailWeight k q (logTorus y) : ℝ≥0∞))

instance : SigmaFinite (diagonalWeightMeasure k q) := SigmaFinite.withDensity _

/-- The outer Haar measure after separating the later rectangle and upper unipotent tail. -/
def outerMeasure (μ : AdditiveHaarMeasure ℂ) (κ : Measure (Compact Size)) : Measure (Outer k q) :=
  (((complexGeneralLinearHaar k).prod (diagonalWeightMeasure k q)).prod κ).prod (rowMeasure μ k)

private theorem tailWeight_chart (p : (Y × N) × Compact TailSize) :
    consecutiveTailWeight k q (tailChart p) = consecutiveTailWeight k q (logTorus p.1.1) := by
  have hu : complexAbsHom p.2.val.val.det = 1 := by
    apply NNReal.eq
    rw [coe_complexAbsHom, NNReal.coe_one]
    have h := normSqC_det_unitary p.2
    change ((‖p.2.val.val.det‖ ^ 2 : ℝ) : ℂ) = 1 at h
    exact_mod_cast h
  simp only [consecutiveTailWeight, tailChart, Units.val_mul, Matrix.det_mul, map_mul, hu, one_mul,
    det_upperUnipotent, mul_one]

private theorem weighted_tailHaar (μ : AdditiveHaarMeasure ℂ) :
    ∃ c : ℝ≥0, 0 < c ∧ (complexGeneralLinearHaar TailSize).withDensity
      (fun g => (consecutiveTailWeight k q g : ℝ≥0∞)) =
      c • (((diagonalWeightMeasure k q).prod (entryHaar μ TailSize)).prod (tailCompactMeasure q)).map tailChart := by
  let η := entryHaar μ TailSize
  let κ := tailCompactMeasure q
  let δ := tailDiagonalMeasure q
  let : SigmaFinite η := entryHaar_sigmaFinite μ TailSize
  let : SecondCountableTopology N := (Langlands.GeneralLinear.upperEntryCoordinates (K := ℂ) TailSize).secondCountableTopology
  let : SecondCountableTopology (Compact TailSize) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨c, hc, h⟩ := complexGapTailIwasawa q μ κ inferInstance
  have hm := (continuous_tailChart (q := q)).measurable
  have hw := measurable_consecutiveTailWeight k q
  refine ⟨c, hc, ?_⟩
  change (complexGeneralLinearHaar TailSize).withDensity _ = c • (((diagonalWeightMeasure k q).prod η).prod κ).map tailChart
  rw [h]
  change (((c : ℝ≥0∞) • ((δ.prod η).prod κ).map tailChart).withDensity
    (fun g => (consecutiveTailWeight k q g : ℝ≥0∞))) = _
  rw [withDensity_smul_measure, ← map_withDensity_comp _ hm hw]
  have ht (p : (Y × N) × Compact TailSize) :
      ((consecutiveTailWeight k q (tailChart p) : ℝ≥0∞)) = (consecutiveTailWeight k q (logTorus p.1.1) : ℝ≥0∞) := by
    rw [tailWeight_chart]
  simp only [Function.comp_def, ht]
  have h₁ := prod_withDensity_left (μ := δ) (ν := η) (hw.comp continuous_logTorus.measurable)
  have h₂ := prod_withDensity_left (μ := δ.prod η) (ν := κ)
    ((hw.comp continuous_logTorus.measurable).comp measurable_fst)
  exact congrArg (fun ν => (c : ℝ≥0∞) • ν.map tailChart) ((congrArg (fun ν => ν.prod κ) h₁).trans h₂).symm

/-- Haar measure splits into the retained outer variables and the triangular inner variables. -/
def ComplexGapTriangularChartStatement : Prop :=
  ∀ (_hk : 0 < k) (μ : AdditiveHaarMeasure ℂ) (κ : Measure (Compact Size)),
    κ.IsHaarMeasure → κ.IsInvInvariant → ∃ c : ℝ≥0, 0 < c ∧
    complexGeneralLinearHaar Size = c • ((outerMeasure k q μ κ).prod
      ((rectangularMeasure μ k q).prod (entryHaar μ TailSize))).map (triangularRightChart k q)

set_option maxHeartbeats 1200000 in
theorem complexGapTriangularChart : ComplexGapTriangularChartStatement k q := by
  intro hk μ κ hκ hκinv
  let : κ.IsHaarMeasure := hκ
  let : κ.IsMulRightInvariant := Langlands.CompactFactorization.isMulRightInvariant_of_compactSpace κ
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let η := entryHaar μ TailSize
  let : SigmaFinite η := entryHaar_sigmaFinite μ TailSize
  let : SecondCountableTopology N := (Langlands.GeneralLinear.upperEntryCoordinates (K := ℂ) TailSize).secondCountableTopology
  let : SecondCountableTopology (Compact TailSize) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology (Compact Size) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let ρ := complexGeneralLinearHaar k
  let τ := rectangularMeasure μ k TailSize
  let δ := diagonalWeightMeasure k q
  let κ₀ := tailCompactMeasure q
  let ν := ((δ.prod η).prod κ₀)
  let σ := ((ρ.prod ν).prod τ).prod κ
  obtain ⟨c, hc, hRight⟩ := complexGapRightChart k q hk μ κ hκ hκinv
  obtain ⟨d, hd, hTail⟩ := weighted_tailHaar k q μ
  have hw := measurable_consecutiveTailWeight k q
  have hWeight : (((ρ.prod (complexGeneralLinearHaar TailSize)).prod τ).prod κ).withDensity
      (fun p => (consecutiveTailWeight k q p.1.1.2 : ℝ≥0∞)) =
      ((ρ.prod ((complexGeneralLinearHaar TailSize).withDensity
        (fun g => (consecutiveTailWeight k q g : ℝ≥0∞)))).prod τ).prod κ := by
    symm
    rw [prod_withDensity_right hw]
    have h₁ := prod_withDensity_left (μ := ρ.prod (complexGeneralLinearHaar TailSize))
      (ν := τ) (hw.comp measurable_snd)
    have h₂ := prod_withDensity_left (μ := (ρ.prod (complexGeneralLinearHaar TailSize)).prod τ)
      (ν := κ) (hw.comp (measurable_snd.comp measurable_fst))
    exact (congrArg (fun ν => ν.prod κ) h₁).trans h₂
  have hReplace : MeasurePreserving (replaceTail k q) σ
      (((ρ.prod (ν.map tailChart)).prod τ).prod κ) :=
    (((MeasurePreserving.id ρ).prod (show MeasurePreserving tailChart ν (ν.map tailChart) from
      ⟨continuous_tailChart.measurable, rfl⟩)).prod (MeasurePreserving.id τ)).prod (MeasurePreserving.id κ)
  have hSplit := (measurePreserving_finishSplit k q μ δ κ).comp (measurePreserving_foldCompact k q μ δ κ)
  change MeasurePreserving (finishSplit k q ∘ foldCompact k q) σ
    ((outerMeasure k q μ κ).prod ((rectangularMeasure μ k q).prod η)) at hSplit
  refine ⟨c * d, mul_pos hc hd, ?_⟩
  rw [hRight, hWeight, hTail, prod_smul_right, prod_smul_left, prod_smul_left,
    Measure.map_smul _ (measurable_consecutiveRightChart k q hk).aemeasurable, smul_smul,
    ← hReplace.map_eq, Measure.map_map (measurable_consecutiveRightChart k q hk) hReplace.measurable,
    chart_composition, ← Measure.map_map (continuous_triangularRightChart k q).measurable hSplit.measurable,
    hSplit.map_eq]

end Langlands.Global.RankinSelbergGlobal.ComplexGapTriangularChart
