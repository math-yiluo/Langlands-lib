import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleCoordinates
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# Exact supplied Haar measure on the two dominant rectangles

The determinant-one laws of the actual multipliers imply preservation of the
supplied product measure. Both rectangle dimensions may be zero.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear HarmonicAnalysis TwoBlockLowerUnipotentQuotient

universe uF uE

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rectangleHaarTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance rectangleHaarValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance rectangleHaarLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance rectangleHaarSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance rectangleHaarMeasurable : MeasurableSpace F.Carrier := borel _
local instance rectangleHaarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance rectangleMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
local instance rectangleMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F.Carrier))
local instance rectanglesBorel (m : Fin 2 → ℕ) (j k : ℕ) :
    BorelSpace (Rectangles m j k F.Carrier) :=
  inferInstanceAs (BorelSpace
    (Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier ×
      Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier))

/-- The exact nested product of the supplied scalar additive Haar measure. -/
def rectangleMeasure (m : Fin 2 → ℕ) (j k : ℕ)
    (ν : AdditiveHaarMeasure F.Carrier) : Measure (Rectangles m j k F.Carrier) :=
  (rectangularMeasure ν (m 0 + 1) k).prod (rectangularMeasure ν j (m 1 + 1))

theorem rectangleMeasure_eq (m : Fin 2 → ℕ) (j k : ℕ)
    (ν : AdditiveHaarMeasure F.Carrier) :
    rectangleMeasure F m j k ν =
      (rectangularMeasure ν (m 0 + 1) k).prod
        (rectangularMeasure ν j (m 1 + 1)) := rfl

instance rectangleMeasure_sigmaFinite (m : Fin 2 → ℕ) (j k : ℕ)
    (ν : AdditiveHaarMeasure F.Carrier) :
    SigmaFinite (rectangleMeasure F m j k ν) := by
  unfold rectangleMeasure
  infer_instance

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The already constructed rectangle equivalence, with its proved topology. -/
def rectangleChangeHomeomorph (j k : ℕ) (u : lowerBlockUnipotent h F.Carrier) :
    Rectangles m j k F.Carrier ≃ₜ Rectangles m j k F.Carrier where
  toEquiv := (rectangleChange h j k u).toEquiv
  continuous_toFun := continuous_rectangleChange h j k u
  continuous_invFun := continuous_rectangleChange_symm h j k u

private theorem determinantNorm_of_det_one {n : ℕ} (A : GeneralLinear n F.Carrier)
    (hA : Matrix.det A.val = 1) :
    F.canonicalTopologicalData.determinantNorm n A = 1 := by
  have hd : GeneralLinear.determinant A = 1 := Units.ext hA
  change F.canonicalTopologicalData.normalizedAbsUnits
    (GeneralLinear.determinant A) = 1
  rw [hd, map_one]

/-- The actual simultaneous change preserves the exact product for every supplied
additive Haar, including either empty rectangle. No Jacobian premise is required. -/
theorem measurePreserving_rectangleChange (j k : ℕ)
    (ν : AdditiveHaarMeasure F.Carrier) (u : lowerBlockUnipotent h F.Carrier) :
    MeasurePreserving (rectangleChange h j k u)
      (rectangleMeasure F m j k ν) (rectangleMeasure F m j k ν) := by
  have hA := determinantNorm_of_det_one F (leftMultiplier h u) (det_leftMultiplier h u)
  have hB := determinantNorm_of_det_one F (rightMultiplier h u) (det_rightMultiplier h u)
  have hx : MeasurePreserving
      (fun x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier =>
        ((leftMultiplier h u)⁻¹).val * x)
      (rectangularMeasure ν (m 0 + 1) k) (rectangularMeasure ν (m 0 + 1) k) := by
    refine ⟨(continuous_const.matrix_mul continuous_id).measurable, ?_⟩
    have hs := padicRectangularHaarScaling F F.canonicalTopologicalData (m 0 + 1) k
      (rectangularMeasure ν (m 0 + 1) k) (leftMultiplier h u)⁻¹ 1
    simpa only [map_inv, hA, inv_one, map_one, Units.val_one, one_pow, div_one,
      one_smul, Matrix.mul_one] using hs
  have hy : MeasurePreserving
      (fun y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
        y * (rightMultiplier h u).val)
      (rectangularMeasure ν j (m 1 + 1)) (rectangularMeasure ν j (m 1 + 1)) := by
    refine ⟨(continuous_id.matrix_mul continuous_const).measurable, ?_⟩
    have hs := padicRectangularHaarScaling F F.canonicalTopologicalData j (m 1 + 1)
      (rectangularMeasure ν j (m 1 + 1)) 1 (rightMultiplier h u)⁻¹
    simpa only [map_inv, hB, inv_one, inv_inv, map_one, Units.val_one, one_pow,
      div_one, one_smul, Matrix.one_mul] using hs
  exact hx.prod hy

/-- Preservation by the actual inverse equivalence, with the same supplied measure. -/
theorem measurePreserving_rectangleChange_symm (j k : ℕ)
    (ν : AdditiveHaarMeasure F.Carrier) (u : lowerBlockUnipotent h F.Carrier) :
    MeasurePreserving (rectangleChange h j k u).symm
      (rectangleMeasure F m j k ν) (rectangleMeasure F m j k ν) :=
  MeasurePreserving.symm (rectangleChangeHomeomorph F h j k u).toMeasurableEquiv
    (measurePreserving_rectangleChange F h j k ν u)

/-- Total Bochner change of variables; it does not assert integrability. -/
theorem integral_rectangleChange {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j k : ℕ) (ν : AdditiveHaarMeasure F.Carrier)
    (u : lowerBlockUnipotent h F.Carrier) (φ : Rectangles m j k F.Carrier → E) :
    (∫ z, φ (rectangleChange h j k u z) ∂rectangleMeasure F m j k ν) =
      ∫ z, φ z ∂rectangleMeasure F m j k ν :=
  (measurePreserving_rectangleChange F h j k ν u).integral_comp
    (rectangleChangeHomeomorph F h j k u).measurableEmbedding φ

/-- Actual integrability is equivalent in both directions, for arbitrary inputs. -/
theorem integrable_rectangleChange_iff {E : Type uE} [NormedAddCommGroup E]
    (j k : ℕ) (ν : AdditiveHaarMeasure F.Carrier)
    (u : lowerBlockUnipotent h F.Carrier) (φ : Rectangles m j k F.Carrier → E) :
    Integrable (fun z => φ (rectangleChange h j k u z)) (rectangleMeasure F m j k ν) ↔
      Integrable φ (rectangleMeasure F m j k ν) :=
  (measurePreserving_rectangleChange F h j k ν u).integrable_comp_emb
    (rectangleChangeHomeomorph F h j k u).measurableEmbedding

end Langlands.RankinSelberg.TwoBlockDominantRectangular
