import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionTransport
import Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution

/-! # Supplied-Haar transport for the reflected first rectangle -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockFirstBlockLaurent
open scoped NNReal

universe uK uF uE

section Coordinates

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

/-- The actual reflected rectangle substitution with its explicit continuous inverse. -/
def firstBlockReflectedRectangleHomeomorph {a q : ℕ} (v : GeneralLinear a K) :
    Matrix (Fin q) (Fin a) K ≃ₜ Matrix (Fin a) (Fin q) K where
  toFun := firstBlockReflectedRectangle v
  invFun X := ((v⁻¹).val * (weylLong a K).val * (-X)).transpose
  left_inv z := by
    have hvw : v⁻¹ * weylLong a K * weylLong a K * v = 1 := by
      rw [mul_assoc v⁻¹, weylLong_mul_self]
      simp
    simp only [firstBlockReflectedRectangle, Matrix.neg_mul, neg_neg]
    calc
      _ = ((v⁻¹ * weylLong a K * weylLong a K * v).val * z.transpose).transpose := by
        simp only [Units.val_mul, Matrix.mul_assoc]
      _ = z := by rw [hvw]; simp
  right_inv X := by
    have hvw : weylLong a K * v * v⁻¹ * weylLong a K = 1 := by
      rw [mul_assoc (weylLong a K), mul_inv_cancel, mul_one, weylLong_mul_self]
    simp only [firstBlockReflectedRectangle, Matrix.transpose_transpose,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    calc
      _ = (weylLong a K * v * v⁻¹ * weylLong a K).val * X := by
        simp only [Units.val_mul, Matrix.mul_assoc]
      _ = X := by rw [hvw]; simp
  continuous_toFun :=
    (continuous_const.matrix_mul continuous_const).matrix_mul continuous_id.matrix_transpose
  continuous_invFun :=
    ((continuous_const.matrix_mul continuous_const).matrix_mul continuous_neg).matrix_transpose

end Coordinates

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reflectionMeasureTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance reflectionMeasureValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance reflectionMeasureLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance reflectionMeasureCountable : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
local instance reflectionMeasureT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance reflectionMeasureMeasurable : MeasurableSpace F.Carrier := borel _
local instance reflectionMeasureBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance reflectionMeasureMatrixBorel (a q : ℕ) : BorelSpace (Matrix (Fin a) (Fin q) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin a → Fin q → F.Carrier))

variable (ν : AdditiveHaarMeasure F.Carrier) {a q : ℕ} (v : GeneralLinear a F.Carrier)

/-- Transpose, unsigned Weyl and negation retain the supplied scalar Haar;
left multiplication contributes exactly the inverse determinant power. -/
theorem rectangularMeasure_map_firstBlockReflectedRectangle :
    (rectangularMeasure ν q a).map (firstBlockReflectedRectangle v) =
      ((F.canonicalTopologicalData.determinantNorm a v : ℝ≥0) ^ q)⁻¹ •
        rectangularMeasure ν a q := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have : LocallyCompactSpace F.Carrier := inferInstance
  have : ν.measure.IsNegInvariant := inferInstance
  have : (rectangularMeasure ν a q).IsNegInvariant := by
    change (Measure.pi (fun _ : Fin a => Measure.pi (fun _ : Fin q => ν.measure))).IsNegInvariant
    infer_instance
  have hT := GodementJacquet.measurePreserving_transpose_rectangularMeasure ν q a
  have hw : F.canonicalTopologicalData.determinantNorm a (weylLong a F.Carrier) = 1 := by
    apply Units.ext
    apply NNReal.eq
    exact abv_det_weylLong (normalizedAbsoluteValue F.canonicalTopologicalData) a
  have hL := padicRectangularHaarScaling F F.canonicalTopologicalData a q
    (rectangularMeasure ν a q) (weylLong a F.Carrier * v) 1
  simp only [inv_one, map_one, Units.val_one, one_pow, div_one, Matrix.mul_one,
    map_mul, hw, one_mul] at hL
  have hm : Measurable (fun X : Matrix (Fin a) (Fin q) F.Carrier =>
      (weylLong a F.Carrier * v).val * X) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hfun : firstBlockReflectedRectangle v =
      (fun X : Matrix (Fin a) (Fin q) F.Carrier => -X) ∘
        ((fun X => (weylLong a F.Carrier * v).val * X) ∘
          (GodementJacquet.transposeMeasurableEquiv q a)) := by
    funext z
    simp [firstBlockReflectedRectangle, Matrix.neg_mul, GodementJacquet.transposeMeasurableEquiv]
  rw [hfun, ← Measure.map_map measurable_neg (hm.comp hT.measurable),
    ← Measure.map_map hm hT.measurable, hT.map_eq, hL,
    Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_neg_eq_self]

/-- Bochner substitution with the exact supplied-Haar determinant factor. -/
theorem integral_firstBlockReflectedRectangle
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Matrix (Fin a) (Fin q) F.Carrier → E) :
    (∫ z, φ (firstBlockReflectedRectangle v z) ∂rectangularMeasure ν q a) =
      (((F.canonicalTopologicalData.determinantNorm a v : ℝ≥0) ^ q)⁻¹ : ℝ≥0) •
        ∫ X, φ X ∂rectangularMeasure ν a q := by
  change (∫ z, φ ((firstBlockReflectedRectangleHomeomorph v).toMeasurableEquiv z)
    ∂rectangularMeasure ν q a) = _
  rw [← integral_map_equiv (firstBlockReflectedRectangleHomeomorph v).toMeasurableEquiv φ]
  change (∫ X, φ X ∂(rectangularMeasure ν q a).map (firstBlockReflectedRectangle v)) = _
  rw [rectangularMeasure_map_firstBlockReflectedRectangle, integral_smul_nnreal_measure]

/-- Absolute integrability is transported independently of the Bochner identity. -/
theorem integrable_firstBlockReflectedRectangle_iff
    {E : Type uE} [NormedAddCommGroup E]
    (φ : Matrix (Fin a) (Fin q) F.Carrier → E) :
    Integrable (fun z => φ (firstBlockReflectedRectangle v z)) (rectangularMeasure ν q a) ↔
      Integrable φ (rectangularMeasure ν a q) := by
  change Integrable (φ ∘ (firstBlockReflectedRectangleHomeomorph v).toMeasurableEquiv)
    (rectangularMeasure ν q a) ↔ _
  rw [← integrable_map_equiv (firstBlockReflectedRectangleHomeomorph v).toMeasurableEquiv φ]
  change Integrable φ ((rectangularMeasure ν q a).map (firstBlockReflectedRectangle v)) ↔ _
  rw [rectangularMeasure_map_firstBlockReflectedRectangle]
  exact integrable_smul_measure (by simp [Units.ne_zero]) (by simp)

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
