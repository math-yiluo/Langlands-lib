import Langlands.Representation.GodementJacquet.ComplexFourierPartition

/-! # The complementary rectangular arrays in Jacquet's Lemma 7.1 -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {m : ℕ}
local notation "I" => Fin m × Fin (m + 1)
local notation "R" => Matrix (Fin m) (Fin (m + 1)) ℂ

/-- Coordinates on the strictly smaller side of the rectangular antidiagonal. -/
abbrev jacquetRectangleLeftIndex (m : ℕ) :=
  {p : Fin m × Fin (m + 1) // p.1.val + p.2.val < m}

/-- The complementary coordinates, including the rectangular antidiagonal. -/
abbrev jacquetRectangleRightIndex (m : ℕ) :=
  {p : Fin m × Fin (m + 1) // ¬ (p.1.val + p.2.val < m)}

local notation "L" => jacquetRectangleLeftIndex m → ℂ
local notation "D" => jacquetRectangleRightIndex m → ℂ

private abbrev rectangleLeft (p : I) : Prop := p.1.val + p.2.val < m

/-- The fixed entries of the primal array. -/
def jacquetRectangleLeftOffset (m : ℕ) : jacquetRectangleRightIndex m → ℂ :=
  fun p => if p.1.1.val + p.1.2.val = m then 1 else 0

/-- The fixed entries of the dual array. -/
def jacquetRectangleRightOffset (m : ℕ) : jacquetRectangleLeftIndex m → ℂ :=
  fun p => if p.1.1.val + p.1.2.val + 1 = m then 1 else 0

/-- The primal array is free strictly before the antidiagonal and has ones
on the antidiagonal. -/
def jacquetRectangleLeftArray (x : L) : R :=
  (complexRectangleUncurry m (m + 1)).symm
    ((complexPartitionCoordinates rectangleLeft).symm (x, jacquetRectangleLeftOffset m))

/-- The dual array is free on and after the antidiagonal and has ones on the
preceding antidiagonal. -/
def jacquetRectangleRightArray (y : D) : R :=
  (complexRectangleUncurry m (m + 1)).symm
    ((complexPartitionCoordinates rectangleLeft).symm (jacquetRectangleRightOffset m, y))

theorem jacquetRectangleLeftArray_free (x : L) (i : Fin m) (j : Fin (m + 1))
    (h : i.val + j.val < m) : jacquetRectangleLeftArray x i j = x ⟨(i, j), h⟩ :=
  complexPartitionCoordinates_symm_apply_left rectangleLeft x _ (i, j) h

theorem jacquetRectangleLeftArray_fixed (x : L) (i : Fin m) (j : Fin (m + 1))
    (h : ¬i.val + j.val < m) : jacquetRectangleLeftArray x i j =
      if i.val + j.val = m then 1 else 0 :=
  complexPartitionCoordinates_symm_apply_right rectangleLeft x _ (i, j) h

theorem jacquetRectangleRightArray_free (y : D) (i : Fin m) (j : Fin (m + 1))
    (h : ¬i.val + j.val < m) : jacquetRectangleRightArray y i j = y ⟨(i, j), h⟩ :=
  complexPartitionCoordinates_symm_apply_right rectangleLeft _ y (i, j) h

theorem jacquetRectangleRightArray_fixed (y : D) (i : Fin m) (j : Fin (m + 1))
    (h : i.val + j.val < m) : jacquetRectangleRightArray y i j =
      if i.val + j.val + 1 = m then 1 else 0 :=
  complexPartitionCoordinates_symm_apply_left rectangleLeft _ y (i, j) h

/-- Jacquet's complementary rectangular arrays satisfy the negative Fourier
identity with the inverse character on the primal side. -/
theorem integral_complexJacquetRectangle_affine (a : ℂˣ) (Φ : SchwartzMap R ℂ) :
    Integrable (fun y : D =>
      rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure a)
        Φ (jacquetRectangleRightArray y) *
        traceCharacter a (complexCoordinatePair (jacquetRectangleLeftOffset m) y))
      (complexCoordinateMeasure (jacquetRectangleRightIndex m) a) ∧
    Integrable (fun x : L => Φ (jacquetRectangleLeftArray x) *
      traceCharacter a (-complexCoordinatePair x (jacquetRectangleRightOffset m)))
      (complexCoordinateMeasure (jacquetRectangleLeftIndex m) a) ∧
    (∫ y : D, rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure a)
      Φ (jacquetRectangleRightArray y) * traceCharacter a (complexCoordinatePair (jacquetRectangleLeftOffset m) y)
      ∂complexCoordinateMeasure (jacquetRectangleRightIndex m) a) =
    ∫ x : L, Φ (jacquetRectangleLeftArray x) *
      traceCharacter a (-complexCoordinatePair x (jacquetRectangleRightOffset m))
      ∂complexCoordinateMeasure (jacquetRectangleLeftIndex m) a := by
  let E := complexRectangleUncurry m (m + 1)
  let Ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm Φ
  have h := integral_complexCoordinateFourier_partition rectangleLeft (-a) Ψ
    (jacquetRectangleRightOffset m) (jacquetRectangleLeftOffset m)
  have hf (z : I → ℂ) :
      complexCoordinateFourier (-a) Ψ z =
        rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure a) Φ (E.symm z) := by
    have hh := complexCoordinateFourier_rectangleUncurry (-a) (Φ : R → ℂ) z
    rw [complexSelfDualMeasure_neg_scale] at hh
    exact hh
  simp only [hf, traceCharacter_neg_scale, neg_neg] at h
  simpa only [complexCoordinateMeasure, complexSelfDualMeasure_neg_scale, Ψ,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, E,
    jacquetRectangleLeftArray, jacquetRectangleRightArray] using h

end Langlands.GodementJacquet
