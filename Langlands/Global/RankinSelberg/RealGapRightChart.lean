import Langlands.Global.RankinSelberg.RealGapUpperTail
import Langlands.Global.RankinSelberg.RealTwoBlockEntries

/-! # The real consecutive-block right Haar chart -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapRightChart

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (blockSum rankInclusion reindex)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.ProductLeviChamber (twoBlock twoBlock_index_val)
open Langlands.RankinSelberg (rectangularMeasure)
open RealGapUpperTail (packedTail)
open RealTwoBlockHaar

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "X" => fun k m => Matrix (Fin k) (Fin m) ℝ
local notation "Coords" => fun k m n => ((G k × G m) × X k m) × K n

local instance gapRightGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapRightGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapRightGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance gapRightGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

section Entries

variable {n k : ℕ} (hk : 0 < k) (hkn : k < n)
local notation "B" => twoBlock n k hk hkn
local notation "e" => finCongr (Nat.add_sub_of_le hkn.le)

private theorem first_index (i : Fin k) : (B).index (0 : Fin 2) i = e (i.castAdd (n - k)) := by
  apply Fin.ext
  rw [twoBlock_index_val]
  simp

private theorem second_index (i : Fin (n - k)) : (B).index (1 : Fin 2) i = e (i.natAdd k) := by
  apply Fin.ext
  rw [twoBlock_index_val]
  rfl

private theorem upperRectangle_val (Y : X k (n - k)) :
    (upperRectangle hk hkn Y).val = Matrix.reindex e e
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 : X k k) Y 0 (1 : X (n - k) (n - k)))) := by
  let shape := twoBlock n k hk hkn
  let u := (rectangleCoordinates hk hkn).symm Y
  let C := shape.radicalCoordinates ℝ u
  let P : shape.UpperPair := ⟨((0 : Fin 2), (1 : Fin 2)), by change (0 : ℕ) < 1; decide⟩
  have hC : C P = Y := (rectangleCoordinates hk hkn).apply_symm_apply Y
  ext i j
  obtain ⟨i, rfl⟩ := (e).surjective i
  obtain ⟨j, rfl⟩ := (e).surjective j
  change u.val.val.val (e i) (e j) = _
  rw [← show ((shape.radicalCoordinates ℝ).symm C).val.val.val = u.val.val.val from
    congrArg (fun w => w.val.val.val) ((shape.radicalCoordinates ℝ).symm_apply_apply u)]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine Fin.addCases (m := k) (n := n - k) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := n - k) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [← first_index hk hkn, ← first_index hk hkn,
      shape.radicalCoordinates_symm_apply_same ℝ C (0 : Fin 2)]
    simp only [finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
  · rw [← first_index hk hkn, ← second_index hk hkn,
      shape.radicalCoordinates_symm_apply_upper ℝ C (show (0 : Fin 2) < 1 by decide)]
    change C P i₀ j₁ = _
    rw [hC]
    simp
  · rw [← second_index hk hkn, ← first_index hk hkn,
      shape.radicalCoordinates_symm_apply_lower ℝ C (show (0 : Fin 2) < 1 by decide)]
    simp
  · rw [← second_index hk hkn, ← second_index hk hkn,
      shape.radicalCoordinates_symm_apply_same ℝ C (1 : Fin 2)]
    simp only [finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

end Entries

/-- Transport between equal dimensions of the real general linear group. -/
def groupCongr {m n : ℕ} (h : m = n) : G m ≃ᵐ G n := by
  subst n
  exact MeasurableEquiv.refl _

/-- Transport a rectangle along an equality of its column counts. -/
def rectangleCongr (k : ℕ) {m n : ℕ} (h : m = n) : X k m ≃ᵐ X k n := by
  subst n
  exact MeasurableEquiv.refl _

private theorem isHaarMeasure_map_groupCongr {m n : ℕ} (h : m = n) (μ : Measure (G m))
    [μ.IsHaarMeasure] : (μ.map (groupCongr h)).IsHaarMeasure := by
  subst n
  change (μ.map id).IsHaarMeasure
  rw [Measure.map_id]
  infer_instance

private theorem measurePreserving_rectangleCongr (μ : AdditiveHaarMeasure ℝ) (k : ℕ) {m n : ℕ} (h : m = n) :
    MeasurePreserving (rectangleCongr k h) (rectangularMeasure μ k m) (rectangularMeasure μ k n) := by
  subst n
  exact MeasurePreserving.id _

private theorem groupCongr_val_det {m n : ℕ} (h : m = n) (g : G m) : (groupCongr h g).val.det = g.val.det := by
  subst n
  rfl

private theorem groupCongr_one {m n : ℕ} (h : m = n) : groupCongr h (1 : G m) = 1 := by
  subst n
  rfl

private theorem reindex_blockSum_groupCongr {k m n : ℕ} (h : m = n) (e : k + n = k + m)
    (g : G k) (z : G m) :
    reindex (finCongr e) (blockSum (g, groupCongr h z)) = blockSum (g, z) := by
  subst n
  apply Units.ext
  ext i j
  rfl

private theorem reindex_rectangleCongr {k m n : ℕ} (h : m = n) (e : k + n = k + m) (Y : X k m) :
    Matrix.reindex (finCongr e) (finCongr e)
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 : X k k) (rectangleCongr k h Y) 0 (1 : X n n))) =
      Matrix.reindex (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k + m)) finSumFinEquiv
        (Matrix.fromBlocks (1 : X k k) Y 0 (1 : X m m)) := by
  subst n
  rfl

variable (k q : ℕ)
local notation "n" => k + q + 1
local notation "m" => q + 1

/-- The count of trailing rows in the consecutive block coordinates. -/
theorem tailSize : m = n - k := by omega

private theorem primeBlock_eq (hk : 0 < k) (hkn : k < n) (g : G k) (z : G m) :
    diagonalBlocks hk hkn g (groupCongr (tailSize k q) z) = blockSum (g, z) := by
  rw [realTwoBlockEntries n k hk hkn]
  exact reindex_blockSum_groupCongr (tailSize k q) _ g z

private theorem upperBlock_eq (hk : 0 < k) (hkn : k < n) (Y : X k m) :
    upperRectangle hk hkn (rectangleCongr k (tailSize k q) Y) = (packedTail k q Y 1).val := by
  apply Units.ext
  rw [upperRectangle_val]
  exact reindex_rectangleCongr (tailSize k q) (Nat.add_sub_of_le hkn.le) Y

/-- The general two-block right-tail factor in the consecutive block sizes. -/
theorem rightTail_eq_consecutive (hk : 0 < k) (hkn : k < n) (z : G m)
    (Y : X k m) (u : K n) :
    rightTail hk hkn (groupCongr (tailSize k q) z) (rectangleCongr k (tailSize k q) Y) u =
      u.val * blockSum (1, z) * (packedTail k q Y 1).val := by
  rw [rightTail, primeBlock_eq, upperBlock_eq]

/-- The full group chart with explicitly consecutive leading and trailing sizes. -/
def consecutiveRightChart (p : Coords k m n) : G n :=
  p.2.val * blockSum (1, p.1.1.2) * (packedTail k q p.1.2 1).val * rankInclusion m p.1.1.1

private def coordCongr : Coords k m n ≃ᵐ Coords k (n - k) n :=
  (((MeasurableEquiv.refl (G k)).prodCongr (groupCongr (tailSize k q))).prodCongr
    (rectangleCongr k (tailSize k q))).prodCongr (MeasurableEquiv.refl _)

private theorem chart_eq (hk : 0 < k) (hkn : k < n) :
    (fun p : Coords k (n - k) n =>
      rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1) ∘ coordCongr k q =
      consecutiveRightChart k q := by
  funext p
  change p.2.val * diagonalBlocks hk hkn 1 (groupCongr (tailSize k q) p.1.1.2) *
      upperRectangle hk hkn (rectangleCongr k (tailSize k q) p.1.2) * diagonalBlocks hk hkn p.1.1.1 1 = _
  rw [primeBlock_eq, upperBlock_eq, ← groupCongr_one (tailSize k q), primeBlock_eq]
  rfl

theorem measurable_consecutiveRightChart (hk : 0 < k) : Measurable (consecutiveRightChart k q) := by
  have hkn : k < n := by omega
  rw [← chart_eq k q hk hkn]
  exact (measurable_rightChart hk hkn).comp (coordCongr k q).measurable

/-- The density supplied by the right-tail chart, as a function of the tail alone. -/
def consecutiveTailWeight (g : G m) : ℝ≥0 := (‖g.val.det‖₊ ^ k)⁻¹

theorem measurable_consecutiveTailWeight : Measurable (fun g : G m => (consecutiveTailWeight k q g : ℝ≥0∞)) :=
  ((continuous_nnnorm.comp Units.continuous_val.matrix_det).pow k).measurable.inv.coe_nnreal_ennreal

/-- Densities pulled back along a measurable chart push forward to the corresponding
weighted image measure. -/
theorem map_withDensity_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) {f : A → B} (hf : Measurable f) {w : B → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF hf]
  change (∫⁻ a, (F ∘ f) a ∂μ.withDensity (w ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hw.comp hf) (hF.comp hf),
    lintegral_withDensity_eq_lintegral_mul _ hw hF, lintegral_map (hw.mul hF) hf]
  rfl

/-- Right Haar measure in the consecutive-block chart, with the tail determinant density. -/
def RealGapRightChartStatement : Prop :=
  ∀ (_hk : 0 < k) (μ : AdditiveHaarMeasure ℝ) (η : Measure (G n)) (η₁ : Measure (G k))
    (η₂ : Measure (G m)) (κ : Measure (K n)),
    η.IsHaarMeasure → η₁.IsHaarMeasure → η₂.IsHaarMeasure →
    κ.IsHaarMeasure → κ.IsInvInvariant → ∃ c : ℝ≥0, 0 < c ∧
    let ν := ((η₁.prod η₂).prod (rectangularMeasure μ k m)).prod κ
    η = c •
      (ν.withDensity fun p => (consecutiveTailWeight k q p.1.1.2 : ℝ≥0∞)).map (consecutiveRightChart k q)

set_option maxHeartbeats 750000 in
theorem realGapRightChart : RealGapRightChartStatement k q := by
  intro hk μ η η₁ η₂ κ hη hη₁ hη₂ hκ hκinv
  have hkn : k < n := by omega
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : η₂.IsHaarMeasure := hη₂
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let η₂' := η₂.map (groupCongr (tailSize k q))
  let : η₂'.IsHaarMeasure := isHaarMeasure_map_groupCongr (tailSize k q) η₂
  let ν := ((η₁.prod η₂).prod (rectangularMeasure μ k m)).prod κ
  let ρ := ((η₁.prod η₂').prod (rectangularMeasure μ k (n - k))).prod κ
  let h := coordCongr k q
  let f (p : Coords k (n - k) n) := rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1
  let w (p : Coords k (n - k) n) := (rightTailWeight (k := k) p.1.1.2 : ℝ≥0∞)
  have hw : Measurable w :=
    ((continuous_nnnorm.comp Units.continuous_val.matrix_det).pow k).measurable.inv.coe_nnreal_ennreal.comp
      (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hν : MeasurePreserving h ν ρ :=
    (((MeasurePreserving.id η₁).prod ⟨(groupCongr (tailSize k q)).measurable, rfl⟩).prod
      (measurePreserving_rectangleCongr μ k (tailSize k q))).prod (MeasurePreserving.id κ)
  have he : w ∘ h = fun p => (consecutiveTailWeight k q p.1.1.2 : ℝ≥0∞) := by
    funext p
    change ((((‖(groupCongr (tailSize k q) p.1.1.2).val.det‖₊ ^ k)⁻¹ : ℝ≥0) : ℝ≥0∞)) = _
    rw [groupCongr_val_det]
    rfl
  obtain ⟨c, hc, hHaar⟩ := realTwoBlockRightHaar n k hk hkn μ η η₁ η₂' κ hη inferInstance
    inferInstance hκ hκinv
  change η = c • (ρ.withDensity w).map f at hHaar
  refine ⟨c, hc, ?_⟩
  change η = c • (ν.withDensity _).map _
  rw [hHaar, ← hν.map_eq, ← map_withDensity_comp _ h.measurable hw,
    Measure.map_map (measurable_rightChart hk hkn) h.measurable,
    chart_eq k q hk hkn, he]

end Langlands.Global.RankinSelbergGlobal.RealGapRightChart
