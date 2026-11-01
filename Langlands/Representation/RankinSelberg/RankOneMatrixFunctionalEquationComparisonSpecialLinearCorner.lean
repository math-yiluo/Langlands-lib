import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxCoefficient
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion

/-! # Determinant-one corner parameters and their scalar measure transport -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.RankOneIwasawa

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Conductor RankOneBox
open scoped NNReal ENNReal

universe uF

section Algebra

variable {E : Type*} [Field E]

/-- The scalar diagonal in the first coordinate, for every ambient size `n + 1`. -/
def rankOneDiagonal (n : ℕ) (g : Langlands.GeneralLinear (0 + 1) E) :
    Langlands.GeneralLinear (n + 1) E :=
  Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1)

/-- The `GL₁` coordinate whose determinant is the determinant of `k`. -/
def glOneDeterminantLift {n : ℕ} (k : Langlands.GeneralLinear (n + 1) E) :
    Langlands.GeneralLinear (0 + 1) E :=
  Iwasawa.diagonalUnits fun _ => Matrix.GeneralLinearGroup.det k

@[simp]
theorem det_glOneDeterminantLift {n : ℕ} (k : Langlands.GeneralLinear (n + 1) E) :
    Matrix.GeneralLinearGroup.det (glOneDeterminantLift k) =
      Matrix.GeneralLinearGroup.det k := by
  simp [glOneDeterminantLift, det_diagonalUnits]

@[simp]
theorem det_determinantRankOne {n : ℕ} (k : Langlands.GeneralLinear (n + 1) E) :
    Matrix.GeneralLinearGroup.det (determinantRankOne n k) =
      Matrix.GeneralLinearGroup.det k := by
  simp [determinantRankOne, det_diagonalUnits, Fin.prod_univ_succ]

@[simp]
theorem det_rankOneDiagonal {n : ℕ} (g : Langlands.GeneralLinear (0 + 1) E) :
    Matrix.GeneralLinearGroup.det (rankOneDiagonal n g) =
      Matrix.GeneralLinearGroup.det g := by
  simp [rankOneDiagonal, det_diagonalUnits, Fin.prod_univ_succ]

theorem rankOneDiagonal_mul_glOneDeterminantLift {n : ℕ}
    (g : Langlands.GeneralLinear (0 + 1) E) (k : Langlands.GeneralLinear (n + 1) E) :
    rankOneDiagonal n (g * glOneDeterminantLift k) =
      rankOneDiagonal n g * determinantRankOne n k := by
  change Iwasawa.diagonalUnits
      (Fin.cons (Matrix.GeneralLinearGroup.det (g * glOneDeterminantLift k)) 1) =
    Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1) *
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det k) 1)
  rw [map_mul, det_glOneDeterminantLift, ← map_mul]
  congr 1
  funext i
  induction i using Fin.cases <;> simp

variable [TopologicalSpace E] [IsTopologicalRing E]

theorem continuous_glOneDeterminantLift (n : ℕ) :
    Continuous (glOneDeterminantLift (E := E) (n := n)) :=
  continuous_diagonalUnits'.comp (continuous_pi fun _ =>
    Matrix.GeneralLinearGroup.continuous_det)

end Algebra

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance specialLinearCornerTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance specialLinearCornerValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance specialLinearCornerLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance specialLinearCornerT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance specialLinearCornerGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance specialLinearCornerGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance specialLinearCornerUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance specialLinearCornerUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩

/-- Remove the actual determinant of the integral parameter from the corner. -/
def specialLinearCorner {n : ℕ}
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :
    Langlands.GeneralLinear (n + 1) F.Carrier :=
  (determinantRankOne n y.2)⁻¹ * diagPoint F (1, y)

theorem continuous_specialLinearCorner (n : ℕ) :
    Continuous (specialLinearCorner F (n := n)) :=
  ((continuous_determinantRankOne n).comp continuous_snd).inv.mul
    ((continuous_diagPoint F).comp (continuous_const.prodMk continuous_id))

/-- This is an equality of determinants, with no integrality premise. -/
@[simp]
theorem det_specialLinearCorner {n : ℕ}
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :
    Matrix.GeneralLinearGroup.det (specialLinearCorner F y) = 1 := by
  simp [specialLinearCorner, diagPoint, det_diagonalUnits, Fin.prod_univ_succ]

/-- Moving `det k` into the scalar variable gives the literal original point. -/
theorem diagPoint_eq_rankOne_mul_specialLinearCorner {n : ℕ}
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier)
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :
    diagPoint F (g, y) =
      rankOneDiagonal n (g * glOneDeterminantLift y.2) * specialLinearCorner F y := by
  rw [rankOneDiagonal_mul_glOneDeterminantLift, specialLinearCorner,
    mul_assoc, mul_inv_cancel_left]
  have hone : (Fin.cons (1 : F.Carrierˣ) (1 : Fin n → F.Carrierˣ) :
      Fin (n + 1) → F.Carrierˣ) = 1 := by
    funext i
    induction i using Fin.cases <;> simp
  simp only [diagPoint, diagonalUnits_torusCoord, rankOneDiagonal, map_one, hone,
    one_mul, mul_assoc]

/-- The correction has normalized determinant absolute value one on integral `k`. -/
theorem weight_glOneDeterminantLift {n : ℕ}
    (k : Langlands.GeneralLinear (n + 1) F.Carrier) (hk : k ∈ integralSet F n) :
    weight F n (glOneDeterminantLift k, 1) = 1 := by
  rw [weight_glOne, det_glOneDeterminantLift]
  have h : (F.canonicalTopologicalData.normalizedAbsUnits
      (Matrix.GeneralLinearGroup.det k) : ℝ≥0) = 1 := by
    apply NNReal.eq
    rw [F.canonicalTopologicalData.normalizedAbsUnits_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact abv_det_eq_one F hk
  rw [h, one_pow, inv_one]

/-- Multiplication by `det k` preserves the weighted scalar Haar measure. -/
theorem measurePreserving_glOneDeterminantLift {n : ℕ}
    (k : Langlands.GeneralLinear (n + 1) F.Carrier) (hk : k ∈ integralSet F n) :
    MeasurePreserving (fun g => glOneDeterminantLift k * g)
      (glOneMeasure F n) (glOneMeasure F n) := by
  let ω : Langlands.GeneralLinear (0 + 1) F.Carrier →* ℝ≥0 :=
    (weight F n).comp ((MonoidHom.id _).prod 1)
  have hω : Continuous ω := (continuous_weight F n).comp
    (continuous_id.prodMk continuous_const)
  have hωk : ω (glOneDeterminantLift k) = 1 :=
    weight_glOneDeterminantLift F k hk
  have hωki : ω ((glOneDeterminantLift k)⁻¹) = 1 := by
    have h := congrArg ω (mul_inv_cancel (glOneDeterminantLift k))
    simpa only [map_mul, map_one, hωk, one_mul] using h
  refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
  change Measure.map (fun g => glOneDeterminantLift k * g)
    ((generalLinearHaar F.Carrier 0).withDensity fun g => (ω g : ℝ≥0∞)) = _
  rw [map_mul_left_withDensity _ ω hω.measurable, hωki, ENNReal.coe_one, one_smul]
  rfl

/-- Scalar integrals in the original and determinant-one coordinates agree,
including the totalized integral when convergence is not assumed. -/
theorem integral_diagPoint_specialLinearCorner {n : ℕ}
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier)
    (hy : y.2 ∈ integralSet F n)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) :
    (∫ g, f (diagPoint F (g, y)) ∂glOneMeasure F n) =
      ∫ g, f (rankOneDiagonal n g * specialLinearCorner F y) ∂glOneMeasure F n := by
  simp_rw [diagPoint_eq_rankOne_mul_specialLinearCorner F,
    rankOne_mul_comm _ (glOneDeterminantLift y.2)]
  exact (measurePreserving_glOneDeterminantLift F y.2 hy).integral_comp
    (Homeomorph.mulLeft (glOneDeterminantLift y.2)).measurableEmbedding
    (fun g => f (rankOneDiagonal n g * specialLinearCorner F y))

/-- The same scalar substitution preserves genuine absolute convergence. -/
theorem integrable_diagPoint_specialLinearCorner_iff {n : ℕ}
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier)
    (hy : y.2 ∈ integralSet F n)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) :
    Integrable (fun g => f (diagPoint F (g, y))) (glOneMeasure F n) ↔
      Integrable (fun g => f (rankOneDiagonal n g * specialLinearCorner F y))
        (glOneMeasure F n) := by
  simp_rw [diagPoint_eq_rankOne_mul_specialLinearCorner F,
    rankOne_mul_comm _ (glOneDeterminantLift y.2)]
  exact (measurePreserving_glOneDeterminantLift F y.2 hy).integrable_comp_emb
    (g := fun g => f (rankOneDiagonal n g * specialLinearCorner F y))
    (Homeomorph.mulLeft (glOneDeterminantLift y.2)).measurableEmbedding

end Canonical

end Langlands.RankinSelberg.RankOneIwasawa
