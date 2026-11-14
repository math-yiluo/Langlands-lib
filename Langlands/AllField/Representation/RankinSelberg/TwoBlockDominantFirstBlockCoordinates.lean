import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockCoordinates
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
/-! # First-block rectangle coordinates in the dominant calculation -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation integrable_firstBlockRowChange_iff integral_firstBlockRowChange rectangularMeasure_map_firstBlockRowChange
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockDominantRectangular.BlockAlgebra
open scoped NNReal

universe uF uA uB uJ uE

section Algebra


end Algebra

section Affine


end Affine

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance firstCoordinatesSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance firstCoordinatesMeasurable : MeasurableSpace F := borel _
local instance firstCoordinatesBorel : BorelSpace F := ⟨rfl⟩
local instance firstCoordinatesMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F))

variable {a b j : ℕ} (ν : AdditiveHaarMeasure F)
  (v : GeneralLinear a F)
  (Z : Matrix (Fin b) (Fin a) F)

/-- Exact affine Jacobian for the supplied scalar Haar, with no normalization
change and including zero external rows. -/
theorem rectangularMeasure_map_firstBlockRowChange
    (Y : Matrix (Fin j) (Fin b) F) :
    (rectangularMeasure ν j a).map (firstBlockRowChange v Z Y) =
      (((⟨⟩ : LocalFieldData F).determinantNorm a v : ℝ≥0) ^ j)⁻¹ •
        rectangularMeasure ν j a := by
  have hmul : (rectangularMeasure ν j a).map
      (fun U : Matrix (Fin j) (Fin a) F => U * v.val) =
      (((⟨⟩ : LocalFieldData F).determinantNorm a v : ℝ≥0) ^ j)⁻¹ •
        rectangularMeasure ν j a := by
    have h := padicRectangularHaarScaling F (⟨⟩ : LocalFieldData F) j a
      (rectangularMeasure ν j a) 1 v⁻¹
    simpa only [inv_inv, map_one, map_inv, Units.val_one, Units.val_inv_eq_inv_val,
      one_pow, one_div, inv_inv, inv_pow, Matrix.one_mul] using h
  have hm : Measurable (fun U : Matrix (Fin j) (Fin a) F => U * v.val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have ha : Measurable (fun T : Matrix (Fin j) (Fin a) F => T + Y * Z) :=
    (continuous_id.add continuous_const).measurable
  change (rectangularMeasure ν j a).map
    ((fun T => T + Y * Z) ∘ (fun U => U * v.val)) = _
  rw [← Measure.map_map ha hm, hmul,
    Measure.map_smul _ ha.aemeasurable, map_add_right_eq_self]

/-- The Bochner substitution uses the same inverse determinant factor as the
measure identity; it does not infer convergence from a total integral. -/
theorem integral_firstBlockRowChange
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Matrix (Fin j) (Fin b) F)
    (φ : Matrix (Fin j) (Fin a) F → E) :
    (∫ U, φ (U * v.val + Y * Z) ∂rectangularMeasure ν j a) =
      ((((⟨⟩ : LocalFieldData F).determinantNorm a v : ℝ≥0) ^ j)⁻¹ : ℝ≥0) •
        ∫ T, φ T ∂rectangularMeasure ν j a := by
  change (∫ U, φ ((firstBlockRowChange v Z Y).toMeasurableEquiv U)
    ∂rectangularMeasure ν j a) = _
  have hmap := rectangularMeasure_map_firstBlockRowChange F ν v Z Y
  change Measure.map (firstBlockRowChange v Z Y).toMeasurableEquiv
    (rectangularMeasure ν j a) = _ at hmap
  rw [← integral_map_equiv (firstBlockRowChange v Z Y).toMeasurableEquiv φ,
    hmap, integral_smul_nnreal_measure]

/-- Absolute integrability is equivalent under the actual affine change. -/
theorem integrable_firstBlockRowChange_iff
    {E : Type uE} [NormedAddCommGroup E]
    (Y : Matrix (Fin j) (Fin b) F)
    (φ : Matrix (Fin j) (Fin a) F → E) :
    Integrable (fun U => φ (U * v.val + Y * Z)) (rectangularMeasure ν j a) ↔
      Integrable φ (rectangularMeasure ν j a) := by
  change Integrable (φ ∘ (firstBlockRowChange v Z Y).toMeasurableEquiv)
    (rectangularMeasure ν j a) ↔ _
  have hmap := rectangularMeasure_map_firstBlockRowChange F ν v Z Y
  change Measure.map (firstBlockRowChange v Z Y).toMeasurableEquiv
    (rectangularMeasure ν j a) = _ at hmap
  rw [← integrable_map_equiv (firstBlockRowChange v Z Y).toMeasurableEquiv φ,
    hmap]
  exact integrable_smul_measure (by simp [Units.ne_zero]) (by simp)

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
