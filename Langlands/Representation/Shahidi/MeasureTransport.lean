import Langlands.Group.GL.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The weighted measure conversions in Shahidi's normalization -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Langlands.Shahidi

universe u

variable {F : Type u} [Field F] [TopologicalSpace F] [MeasurableSpace F]

section Field

variable [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]

/-- The measure `dz = |z| d*z`, pushed from the nonzero field elements.
No additive Haar or Fourier normalization property is assumed here. -/
def fieldMeasureFromUnits (abv : AbsoluteValue F ℝ) (μ : Measure Fˣ) : Measure F :=
  Measure.map (fun z : Fˣ => (z : F))
    (μ.withDensity (fun z => ENNReal.ofReal (abv (z : F))))

theorem fieldMeasureFromUnits_apply (abv : AbsoluteValue F ℝ) (μ : Measure Fˣ)
    {S : Set F} (hS : MeasurableSet S) :
    fieldMeasureFromUnits abv μ S =
      ∫⁻ z in (fun z : Fˣ => (z : F)) ⁻¹' S,
        ENNReal.ofReal (abv (z : F)) ∂μ := by
  rw [fieldMeasureFromUnits, Measure.map_apply Units.continuous_val.measurable hS,
    withDensity_apply _ (Units.continuous_val.measurable hS)]

@[simp] theorem fieldMeasureFromUnits_smul (abv : AbsoluteValue F ℝ)
    (μ : Measure Fˣ) (c : ℝ≥0∞) :
    fieldMeasureFromUnits abv (c • μ) = c • fieldMeasureFromUnits abv μ := by
  unfold fieldMeasureFromUnits
  rw [withDensity_smul_measure,
    Measure.map_smul c Units.continuous_val.measurable.aemeasurable]

@[simp] theorem fieldMeasureFromUnits_zero [T1Space F]
    (abv : AbsoluteValue F ℝ) (μ : Measure Fˣ) :
    fieldMeasureFromUnits abv μ {0} = 0 := by
  rw [fieldMeasureFromUnits, Measure.map_apply Units.continuous_val.measurable
    (measurableSet_singleton 0)]
  have he : (fun z : Fˣ => (z : F)) ⁻¹' ({0} : Set F) = ∅ := by
    ext z
    simp
  rw [he, measure_empty]

end Field

section Matrix

variable (n : ℕ)
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [BorelSpace (Matrix (Fin n) (Fin n) F)]

/-- The matrix measure `da = |det a|^n d*a`, extended by zero on singular
matrices through the actual inclusion of the general linear group. -/
def matrixMeasureFromGeneralLinear (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear n F)) : Measure (Matrix (Fin n) (Fin n) F) :=
  Measure.map (fun g : GeneralLinear n F => (g : Matrix (Fin n) (Fin n) F))
    (μ.withDensity (fun g => ENNReal.ofReal (abv (g : Matrix (Fin n) (Fin n) F).det) ^ n))

theorem matrixMeasureFromGeneralLinear_apply (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear n F)) {S : Set (Matrix (Fin n) (Fin n) F)}
    (hS : MeasurableSet S) :
    matrixMeasureFromGeneralLinear n abv μ S =
      ∫⁻ g in (fun g : GeneralLinear n F => (g : Matrix (Fin n) (Fin n) F)) ⁻¹' S,
        ENNReal.ofReal (abv (g : Matrix (Fin n) (Fin n) F).det) ^ n ∂μ := by
  rw [matrixMeasureFromGeneralLinear,
    Measure.map_apply Units.continuous_val.measurable hS,
    withDensity_apply _ (Units.continuous_val.measurable hS)]

@[simp] theorem matrixMeasureFromGeneralLinear_smul (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear n F)) (c : ℝ≥0∞) :
    matrixMeasureFromGeneralLinear n abv (c • μ) =
      c • matrixMeasureFromGeneralLinear n abv μ := by
  unfold matrixMeasureFromGeneralLinear
  rw [withDensity_smul_measure,
    Measure.map_smul c Units.continuous_val.measurable.aemeasurable]

/-- The extension puts no mass on the singular locus. This assertion alone
is not an additive Haar-measure theorem. -/
@[simp] theorem matrixMeasureFromGeneralLinear_singular [T2Space F] [IsTopologicalRing F]
    (abv : AbsoluteValue F ℝ) (μ : Measure (GeneralLinear n F)) :
    matrixMeasureFromGeneralLinear n abv μ {a | a.det = 0} = 0 := by
  have hm : MeasurableSet {a : Matrix (Fin n) (Fin n) F | a.det = 0} :=
    (isClosed_eq continuous_id.matrix_det continuous_const).measurableSet
  rw [matrixMeasureFromGeneralLinear, Measure.map_apply Units.continuous_val.measurable hm]
  have he : (fun g : GeneralLinear n F => (g : Matrix (Fin n) (Fin n) F)) ⁻¹'
      {a | a.det = 0} = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  rw [he, measure_empty]

end Matrix

end Langlands.Shahidi
