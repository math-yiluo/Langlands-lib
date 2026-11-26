import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Group.GL.LowerTriangularBigCellConull
import Langlands.Representation.Archimedean.MaximalParabolicIntegration
import Langlands.Analysis.Local.QuotientNormalizingFunction

/-! # The real lower-block quotient chart with one trailing coordinate -/

noncomputable section

open MeasureTheory Set Topology Matrix
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000

namespace Langlands.Global.RankinSelbergGlobal.RealLastPivotChart

open Langlands.GeneralLinear Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow_unipotent_mul lastRow_mul_eq_vecMul)
open Langlands.Archimedean.MaximalParabolicIntegration
open ArchimedeanLocal

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
private local instance (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "L" => Langlands.GeneralLinear (r + 2) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 2) ℝ
local notation "B" => lowerTriangularSubgroup 1 ℝ
local notation "Q" => LeftUnipotentQuotient (r + 1) ℝ
local notation "Params" => LowerBlockQuotientParameters (r + 1) 1 ℝ
local notation "π" => leftQuotientMap N
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "iotaMat" => Langlands.Archimedean.MaximalParabolicIntegration.iota

/-- The lower-right entry of a real matrix. -/
def pivot (g : L) : ℝ := row g (Fin.last (r + 1))

private theorem continuous_pivot : Continuous (pivot (r := r)) :=
  Units.continuous_val.matrix_elem _ _

private theorem pivot_unipotent_mul (n : N) (g : L) : pivot (n.val * g) = pivot g :=
  congrFun (lastRow_unipotent_mul n g) _

private abbrev Cell := {g : L // pivot g ≠ 0}

private theorem isOpen_cell : IsOpen {g : L | pivot g ≠ 0} :=
  isOpen_ne_fun continuous_pivot continuous_const

private def rowMatrix (z : Cell (r := r)) : L := JGL (row z.val) z.property

private theorem continuous_rowMatrix : Continuous (rowMatrix (r := r)) := by
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, rowMatrix, JGL_val]
  apply continuous_matrix
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Jmat, Matrix.of_apply, Fin.lastCases_last, Langlands.RankinSelberg.lastRow]
    exact (Units.continuous_val.comp
      (continuous_subtype_val : Continuous (Subtype.val : Cell (r := r) → L))).matrix_elem (Fin.last (r + 1)) j
  · simpa only [Jmat, Matrix.of_apply, Fin.lastCases_castSucc] using
      (continuous_const : Continuous fun _ : Cell (r := r) => (1 : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ) k.castSucc j)

private def residual (z : Cell (r := r)) : L := z.val * (rowMatrix z)⁻¹

private theorem continuous_residual : Continuous (residual (r := r)) :=
  continuous_subtype_val.mul continuous_rowMatrix.inv

private theorem row_residual (z : Cell (r := r)) : row (residual z) = row (1 : L) := by
  have h : row z.val = row (rowMatrix z) := by
    funext j
    change z.val.val (Fin.last (r + 1)) j = (rowMatrix z).val (Fin.last (r + 1)) j
    simp only [rowMatrix, JGL_val, Jmat, Matrix.of_apply, Fin.lastCases_last, Langlands.RankinSelberg.lastRow]
  rw [residual, lastRow_mul_eq_vecMul, h, ← lastRow_mul_eq_vecMul, mul_inv_cancel]

private theorem residual_last (z : Cell (r := r)) : pivot (residual z) = 1 := by
  simpa only [pivot, Langlands.RankinSelberg.lastRow, Units.val_one, Matrix.one_apply_eq] using
    congrFun (row_residual z) (Fin.last (r + 1))

private theorem residual_prefix (z : Cell (r := r)) (j : Fin (r + 1)) :
    (residual z).val (Fin.last (r + 1)) j.castSucc = 0 := by
  simpa only [Langlands.RankinSelberg.lastRow, Units.val_one, Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm] using
    congrFun (row_residual z) j.castSucc

private def firstMatrix (z : Cell (r := r)) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (topLeft (residual z).val) (by
    have h := (determinant (residual z)).ne_zero
    change (residual z).val.det ≠ 0 at h
    have hLast : (residual z).val (Fin.last (r + 1)) (Fin.last (r + 1)) = 1 := residual_last z
    rwa [det_eq_mul_det_topLeft (residual_prefix z) (by rw [hLast]; exact one_ne_zero),
      hLast, one_mul] at h)

private theorem continuous_firstMatrix : Continuous (firstMatrix (r := r)) := by
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  change Continuous (fun z : Cell (r := r) => topLeft (residual z).val)
  exact (Units.continuous_val.comp continuous_residual).matrix_submatrix _ _

private def trailingScalar (z : Cell (r := r)) : B :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.mk0 (pivot z.val) z.property), by
    rw [mem_lowerTriangularSubgroup_iff]
    intro i j hij
    exact ((Subsingleton.elim i j).not_lt hij).elim⟩

private theorem continuous_trailingScalar : Continuous (trailingScalar (r := r)) := by
  apply Continuous.subtype_mk
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  change Continuous (fun z : Cell (r := r) => Matrix.diagonal (fun _ : Fin 1 => pivot z.val))
  exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_pivot.comp continuous_subtype_val)

private def lastRectangle (g : L) : Matrix (Fin 1) (Fin (r + 1)) ℝ :=
  fun _ j => row g j.castSucc

private theorem continuous_lastRectangle : Continuous (lastRectangle (r := r)) :=
  continuous_matrix fun _ _ => Units.continuous_val.matrix_elem _ _

private def parameters (z : Cell (r := r)) : Params :=
  (leftQuotientMap (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (firstMatrix z),
    lastRectangle z.val, trailingScalar z)

private theorem continuous_parameters : Continuous (parameters (r := r)) :=
  ((leftQuotient_isOpenQuotientMap _).continuous.comp continuous_firstMatrix).prodMk
    ((continuous_lastRectangle.comp continuous_subtype_val).prodMk continuous_trailingScalar)

private theorem residual_factor (z : Cell (r := r)) :
    residual z = (nPU (fun i => (residual z).val i.castSucc (Fin.last (r + 1)))).val *
      iotaGL (firstMatrix z) := by
  apply Units.ext
  have hr := eq_nP_mul_iota_mul_dlast (residual_prefix z)
    (show pivot (residual z) ≠ 0 by rw [residual_last]; exact one_ne_zero)
  change _ = nP _ * iotaMat (topLeft (residual z).val)
  have hOne : dlast (m := r + 1) 1 = 1 := by
    rw [dlast, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Fin.lastCases (by simp) (fun _ => by simp) i
  change _ = nP (fun i => _ / pivot (residual z)) * iotaMat _ * dlast (pivot (residual z)) at hr
  simpa only [residual_last, div_one, hOne, mul_one] using hr

private theorem iota_mul_rowMatrix (z : Cell (r := r)) :
    iotaGL (firstMatrix z) * rowMatrix z =
      lowerBlockPair (firstMatrix z) (lastRectangle z.val) (trailingScalar z) := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, iotaGL_val, rowMatrix, JGL_val]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  · have h := lowerBlockPair_22 (firstMatrix z) (lastRectangle z.val) (trailingScalar z) 0 0
    change (lowerBlockPair (firstMatrix z) (lastRectangle z.val) (trailingScalar z)).val
      (Fin.last (r + 1)) (Fin.last (r + 1)) = _ at h
    rw [h]
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, trailingScalar, pivot,
      Langlands.RankinSelberg.lastRow, Matrix.GeneralLinearGroup.scalar]
  · have h := lowerBlockPair_21 (firstMatrix z) (lastRectangle z.val) (trailingScalar z) 0 j'
    change (lowerBlockPair (firstMatrix z) (lastRectangle z.val) (trailingScalar z)).val
      (Fin.last (r + 1)) j'.castSucc = _ at h
    rw [h]
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, lastRectangle,
      Langlands.RankinSelberg.lastRow]
  · have h := lowerBlockPair_12 (firstMatrix z) (lastRectangle z.val) (trailingScalar z) i' 0
    change (lowerBlockPair (firstMatrix z) (lastRectangle z.val) (trailingScalar z)).val
      i'.castSucc (Fin.last (r + 1)) = 0 at h
    rw [h]
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.one_apply]
  · have h := lowerBlockPair_11 (firstMatrix z) (lastRectangle z.val) (trailingScalar z) i' j'
    change (lowerBlockPair (firstMatrix z) (lastRectangle z.val) (trailingScalar z)).val
      i'.castSucc j'.castSucc = _ at h
    rw [h]
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.one_apply, mul_ite]

private theorem lowerBlockQuotientChart_parameters (z : Cell (r := r)) :
    lowerBlockQuotientChart (parameters z) = π z.val := by
  unfold parameters
  rw [leftQuotientMap_apply, lowerBlockQuotientChart_mk, ← iota_mul_rowMatrix, ← leftQuotientMap_apply]
  have hz : z.val = (nPU (fun i => (residual z).val i.castSucc (Fin.last (r + 1)))).val *
      (iotaGL (firstMatrix z) * rowMatrix z) := by
    rw [← mul_assoc, ← residual_factor, residual, inv_mul_cancel_right]
  rw [hz, leftQuotientMap_subgroup_mul]

private theorem pivot_lowerBlockPair (g : G) (x : Matrix (Fin 1) (Fin (r + 1)) ℝ) (h : B) :
    pivot (r := r) (lowerBlockPair (d := 1) g x h) ≠ 0 := by
  change lowerBlockPair g x h ((0 : Fin 1).natAdd (r + 1)) ((0 : Fin 1).natAdd (r + 1)) ≠ 0
  rw [lowerBlockPair_22, ← Matrix.det_fin_one h.val.val]
  exact (determinant h.val).ne_zero

private theorem exists_parameters_of_mk_mem_image {g : L} {S : Set Params}
    (hg : π g ∈ lowerBlockQuotientChart '' S) : ∃ z : Cell (r := r), z.val = g ∧ parameters z ∈ S := by
  obtain ⟨⟨q, x, h⟩, hw, hq⟩ := hg
  induction q using Quotient.inductionOn with
  | h a =>
    rw [lowerBlockQuotientChart_mk, leftQuotientMap_apply, leftQuotient_mk_eq_iff] at hq
    let b : L := lowerBlockPair (d := 1) a x h
    let n : N := ⟨g * b⁻¹, hq⟩
    have he : n.val * b = g := inv_mul_cancel_right g b
    have hne : pivot g ≠ 0 := by rw [← he, pivot_unipotent_mul]; exact pivot_lowerBlockPair a x h
    let z : Cell (r := r) := ⟨g, hne⟩
    refine ⟨z, rfl, ?_⟩
    have ha : parameters z = (Quotient.mk _ a, x, h) := by
      apply lowerBlockQuotientChart_injective
      rw [lowerBlockQuotientChart_parameters, lowerBlockQuotientChart_mk, leftQuotientMap_apply]
      exact (leftQuotient_mk_eq_iff _ _ _).mpr hq |>.symm
    rwa [ha]

/-- With one trailing coordinate, the lower-block quotient chart is an open embedding. -/
theorem isOpenEmbedding_realLastPivotChart :
    IsOpenEmbedding (lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)) := by
  refine .of_continuous_injective_isOpenMap continuous_lowerBlockQuotientChart
    lowerBlockQuotientChart_injective ?_
  intro S hS
  apply (leftQuotient_isOpenQuotientMap
    (Langlands.GeneralLinear.upperUnipotent (r + 2) ℝ)).isQuotientMap.isCoinducing.isOpen_preimage.mp
  have he : (π ⁻¹' (lowerBlockQuotientChart (a := r + 1) (d := 1) '' S)) =
      Subtype.val '' (parameters (r := r) ⁻¹' S) := by
    ext g
    constructor
    · intro hg
      obtain ⟨z, hzg, hz⟩ := exists_parameters_of_mk_mem_image hg
      exact ⟨z, hz, hzg⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨parameters z, hz, lowerBlockQuotientChart_parameters z⟩
  rw [he]
  exact isOpen_cell.isOpenEmbedding_subtypeVal.isOpenMap _ (hS.preimage continuous_parameters)

/-- A class is in the chart's range exactly when its last entry is nonzero. -/
theorem mem_range_realLastPivotChart (g : L) :
    π g ∈ range (lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)) ↔ pivot g ≠ 0 := by
  constructor
  · intro hg
    have hi : π g ∈ lowerBlockQuotientChart '' (univ : Set Params) := by simpa using hg
    obtain ⟨z, hz, _⟩ := exists_parameters_of_mk_mem_image hi
    exact hz ▸ z.property
  · intro hg
    exact ⟨parameters ⟨g, hg⟩, lowerBlockQuotientChart_parameters ⟨g, hg⟩⟩

private theorem pivot_zero_null (μ : Measure L) [μ.IsHaarMeasure] [μ.InnerRegular] :
    μ {g : L | pivot g = 0} = 0 := by
  have hR : ∀ S ∈ 𝓝 (0 : ℝ), ∃ t ∈ S, t ≠ 0 := by
    intro S hS
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hS
    refine ⟨ε / 2, hsub ?_, by positivity⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  refine measure_mono_null ?_ (haar_setOf_not_upperUnipotent_mul_lowerTriangular hR μ)
  intro g hg
  rintro ⟨u, hu, b, hb, rfl⟩
  change pivot ((⟨u, hu⟩ : N).val * b) = 0 at hg
  rw [pivot_unipotent_mul] at hg
  have hn : b.val.det ≠ 0 := (determinant b).ne_zero
  rw [Matrix.det_of_isLowerTriangular _ hb] at hn
  apply hn
  exact Finset.prod_eq_zero (Finset.mem_univ (Fin.last (r + 1))) hg

/-- The open chart is conull for every compatible real quotient measure. -/
theorem measure_compl_range_realLastPivotChart (D : RealQuotientMeasureData (r + 1)) :
    D.measure (range (lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)))ᶜ = 0 := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let S := (range (lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)))ᶜ
  have hS : MeasurableSet S :=
    (isOpenEmbedding_realLastPivotChart (r := r)).isOpen_range.measurableSet.compl
  have hPre : π ⁻¹' S = {g : L | pivot g = 0} := by
    ext g
    change (¬ π g ∈ range (lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ))) ↔ pivot g = 0
    rw [mem_range_realLastPivotChart, not_not]
  have hZero : D.groupHaar (π ⁻¹' S) = 0 := hPre ▸ pivot_zero_null D.groupHaar
  have hClosed : IsClosed (N : Set L) := UpperUnipotent.isClosed
  obtain ⟨ρ, _, hρ, _⟩ := exists_continuous_isNormalizingFunction N hClosed D.unipotentHaar
  have hπ : Measurable π := (leftQuotient_isOpenQuotientMap N).continuous.measurable
  change D.measure S = 0
  rw [D.compatible.eq_map_withDensity hClosed hρ, Measure.map_apply hπ hS,
    withDensity_apply _ (hπ hS)]
  exact setLIntegral_measure_zero _ _ hZero

/-- The real one-coordinate lower-block quotient chart is an open embedding
whose image has full compatible quotient measure. -/
def RealLastPivotChartStatement : Prop :=
  ∀ r : ℕ,
    IsOpenEmbedding (lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)) ∧
    ∀ D : RealQuotientMeasureData (r + 1),
      D.measure (range (lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)))ᶜ = 0

theorem realLastPivotChart : RealLastPivotChartStatement :=
  fun _ => ⟨isOpenEmbedding_realLastPivotChart, measure_compl_range_realLastPivotChart⟩

end Langlands.Global.RankinSelbergGlobal.RealLastPivotChart
