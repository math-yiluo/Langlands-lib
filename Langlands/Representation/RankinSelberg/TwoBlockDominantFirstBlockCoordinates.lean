import Langlands.Representation.RankinSelberg.TwoBlockDominantBlockAlgebra
import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Mathlib.MeasureTheory.Integral.Prod

/-! # First-block rectangle coordinates in the dominant calculation -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory HarmonicAnalysis TwoBlockDominantRectangular.BlockAlgebra
open scoped NNReal

universe uF uA uB uJ uE

section Algebra

variable {K : Type uF} [CommRing K]
variable {A : Type uA} {B : Type uB} {J : Type uJ}
variable [Fintype A] [Fintype B] [Fintype J]
variable [DecidableEq A] [DecidableEq B] [DecidableEq J]

/-- The small first-block rectangle contains the Jacquet rows `Z` and the
changed external rows `U*v + Y*Z`. -/
theorem firstBlock_three_factorization
    (v : Matrix A A K) (Z : Matrix B A K)
    (U : Matrix J A K) (Y : Matrix J B K) :
    three 1 0 0 0 1 0 U Y 1 * three v 0 0 0 1 0 0 0 1 *
        three 1 0 0 Z 1 0 0 0 1 =
      three v 0 0 Z 1 0 (U*v + Y*Z) 0 1 *
        three 1 0 0 0 1 0 0 Y 1 := by
  simp only [three_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add]

end Algebra

section Affine

variable {K : Type uF} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {a b j : ℕ}

/-- The change in the external first-block rows, for fixed remaining rows. -/
def firstBlockRowChange (v : GeneralLinear a K)
    (Z : Matrix (Fin b) (Fin a) K) (Y : Matrix (Fin j) (Fin b) K) :
    Matrix (Fin j) (Fin a) K ≃ₜ Matrix (Fin j) (Fin a) K where
  toFun U := U * v.val + Y * Z
  invFun T := (T - Y * Z) * (v⁻¹).val
  left_inv U := by
    simp [Matrix.mul_assoc, -Units.val_mul]
  right_inv T := by
    simp [Matrix.mul_assoc, -Units.val_mul]
  continuous_toFun := (continuous_id.matrix_mul continuous_const).add continuous_const
  continuous_invFun := (continuous_id.sub continuous_const).matrix_mul continuous_const

@[simp] theorem firstBlockRowChange_apply (v : GeneralLinear a K)
    (Z : Matrix (Fin b) (Fin a) K) (Y : Matrix (Fin j) (Fin b) K)
    (U : Matrix (Fin j) (Fin a) K) :
    firstBlockRowChange v Z Y U = U * v.val + Y * Z := rfl

@[simp] theorem firstBlockRowChange_symm_apply (v : GeneralLinear a K)
    (Z : Matrix (Fin b) (Fin a) K) (Y : Matrix (Fin j) (Fin b) K)
    (T : Matrix (Fin j) (Fin a) K) :
    (firstBlockRowChange v Z Y).symm T = (T - Y * Z) * (v⁻¹).val := rfl

/-- Simultaneous row change, retaining `Y` as its first coordinate. -/
def firstBlockRectangleChange (v : GeneralLinear a K)
    (Z : Matrix (Fin b) (Fin a) K) :
    (Matrix (Fin j) (Fin b) K × Matrix (Fin j) (Fin a) K) ≃ₜ
      (Matrix (Fin j) (Fin b) K × Matrix (Fin j) (Fin a) K) where
  toFun p := (p.1, firstBlockRowChange v Z p.1 p.2)
  invFun p := (p.1, (firstBlockRowChange v Z p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk
    ((continuous_snd.matrix_mul continuous_const).add
      (continuous_fst.matrix_mul continuous_const))
  continuous_invFun := continuous_fst.prodMk
    ((continuous_snd.sub (continuous_fst.matrix_mul continuous_const)).matrix_mul
      continuous_const)

end Affine

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance firstCoordinatesTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance firstCoordinatesValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance firstCoordinatesLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance firstCoordinatesSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance firstCoordinatesMeasurable : MeasurableSpace F.Carrier := borel _
local instance firstCoordinatesBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance firstCoordinatesMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
local instance firstCoordinatesMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F.Carrier))

variable {a b j : ℕ} (ν : AdditiveHaarMeasure F.Carrier)
  (v : GeneralLinear a F.Carrier)
  (Z : Matrix (Fin b) (Fin a) F.Carrier)

/-- Exact affine Jacobian for the supplied scalar Haar, with no normalization
change and including zero external rows. -/
theorem rectangularMeasure_map_firstBlockRowChange
    (Y : Matrix (Fin j) (Fin b) F.Carrier) :
    (rectangularMeasure ν j a).map (firstBlockRowChange v Z Y) =
      ((F.canonicalTopologicalData.determinantNorm a v : ℝ≥0) ^ j)⁻¹ •
        rectangularMeasure ν j a := by
  have hmul : (rectangularMeasure ν j a).map
      (fun U : Matrix (Fin j) (Fin a) F.Carrier => U * v.val) =
      ((F.canonicalTopologicalData.determinantNorm a v : ℝ≥0) ^ j)⁻¹ •
        rectangularMeasure ν j a := by
    have h := padicRectangularHaarScaling F F.canonicalTopologicalData j a
      (rectangularMeasure ν j a) 1 v⁻¹
    simpa only [inv_inv, map_one, map_inv, Units.val_one, Units.val_inv_eq_inv_val,
      one_pow, one_div, inv_inv, inv_pow, Matrix.one_mul] using h
  have hm : Measurable (fun U : Matrix (Fin j) (Fin a) F.Carrier => U * v.val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have ha : Measurable (fun T : Matrix (Fin j) (Fin a) F.Carrier => T + Y * Z) :=
    (continuous_id.add continuous_const).measurable
  change (rectangularMeasure ν j a).map
    ((fun T => T + Y * Z) ∘ (fun U => U * v.val)) = _
  rw [← Measure.map_map ha hm, hmul,
    Measure.map_smul _ ha.aemeasurable, map_add_right_eq_self]

/-- The Bochner substitution uses the same inverse determinant factor as the
measure identity; it does not infer convergence from a total integral. -/
theorem integral_firstBlockRowChange
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Matrix (Fin j) (Fin b) F.Carrier)
    (φ : Matrix (Fin j) (Fin a) F.Carrier → E) :
    (∫ U, φ (U * v.val + Y * Z) ∂rectangularMeasure ν j a) =
      (((F.canonicalTopologicalData.determinantNorm a v : ℝ≥0) ^ j)⁻¹ : ℝ≥0) •
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
    (Y : Matrix (Fin j) (Fin b) F.Carrier)
    (φ : Matrix (Fin j) (Fin a) F.Carrier → E) :
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

/-- Joint supplied-Haar transport in `Y,U`, so that subsequent Fubini steps
can use the same coordinates as the block factorization. -/
theorem measurePreserving_firstBlockRectangleChange :
    MeasurePreserving (firstBlockRectangleChange (j := j) v Z)
      ((rectangularMeasure ν j b).prod (rectangularMeasure ν j a))
      ((rectangularMeasure ν j b).prod
        (((F.canonicalTopologicalData.determinantNorm a v : ℝ≥0) ^ j)⁻¹ •
          rectangularMeasure ν j a)) := by
  change MeasurePreserving
    (fun p : Matrix (Fin j) (Fin b) F.Carrier × Matrix (Fin j) (Fin a) F.Carrier =>
      (id p.1, firstBlockRowChange v Z p.1 p.2)) _ _
  apply (MeasurePreserving.id (rectangularMeasure ν j b)).skew_product
    (g := fun Y U => firstBlockRowChange v Z Y U)
  · exact ((continuous_snd.matrix_mul continuous_const).add
      (continuous_fst.matrix_mul continuous_const)).measurable
  · exact ae_of_all _ (rectangularMeasure_map_firstBlockRowChange F ν v Z)

end Padic

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
