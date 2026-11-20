import Langlands.Representation.GodementJacquet.ComplexTriangularHaar

/-! # The row scalings from triangular group coordinates to additive matrix entries -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.HarmonicAnalysis

variable {n : ℕ}
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "M" => Matrix I I ℂ
local notation "U" => upperUnipotent n ℂ

/-- A triangular matrix with supplied diagonal and strict upper entries. -/
def complexTriangularMatrix (d : I → ℂ) (X : J → ℂ) : M :=
  Matrix.of fun i j =>
    if h : i < j then X ⟨(i, j), h⟩ else if i = j then d i else 0

theorem continuous_complexTriangularMatrix (d : I → ℂ) : Continuous (complexTriangularMatrix d) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun X : J → ℂ => if h : i < j then X ⟨(i, j), h⟩ else if i = j then d i else 0)
  by_cases h : i < j
  · simp only [h, dite_true]
    exact continuous_apply (⟨(i, j), h⟩ : J)
  · simp only [h, dite_false]
    exact continuous_const

theorem diagonal_mul_upperEntryCoordinates (d : I → ℂˣ) (X : J → ℂ) :
    (diagonalMatrixUnits ℂ d).val * ((upperEntryCoordinates n (K := ℂ)).symm X).val.val =
      complexTriangularMatrix (fun i => (d i : ℂ)) (fun ij => (d ij.1.1 : ℂ) * X ij) := by
  let u : U := (upperEntryCoordinates n).symm X
  ext i j
  change (Matrix.diagonal (fun k => (d k : ℂ)) * u.val.val) i j = _
  rw [Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [u, upperEntryCoordinates_symm_upper X hij, complexTriangularMatrix,
      Matrix.of_apply, hij, dite_true]
  · rw [u.property.2 _, mul_one]
    simp [complexTriangularMatrix]
  · rw [u.property.1 hji, mul_zero]
    simp [complexTriangularMatrix, not_lt_of_gt hji, ne_of_gt hji]

theorem upperEntryCoordinates_mul_diagonal (d : I → ℂˣ) (X : J → ℂ) :
    ((upperEntryCoordinates n (K := ℂ)).symm X).val.val * (diagonalMatrixUnits ℂ d).val =
      complexTriangularMatrix (fun i => (d i : ℂ)) (fun ij => (d ij.1.2 : ℂ) * X ij) := by
  let u : U := (upperEntryCoordinates n).symm X
  ext i j
  change (u.val.val * Matrix.diagonal (fun k => (d k : ℂ))) i j = _
  rw [Matrix.mul_diagonal]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [u, upperEntryCoordinates_symm_upper X hij, complexTriangularMatrix,
      Matrix.of_apply, hij, dite_true, mul_comm]
  · rw [u.property.2 _, one_mul]
    simp [complexTriangularMatrix]
  · rw [u.property.1 hji, zero_mul]
    simp [complexTriangularMatrix, not_lt_of_gt hji, ne_of_gt hji]

private theorem map_scale_upperEntries
    (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure] (a : J → ℂˣ) :
    (upperEntryProductMeasure ν n).map (fun (X : J → ℂ) ij => (a ij : ℂ) * X ij) =
      (∏ ij : J, complexAbsHom (a ij : ℂ))⁻¹ • upperEntryProductMeasure ν n := by
  let D : J → ℂ := fun ij => (a ij : ℂ)
  have hD : (Matrix.diagonal D).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun ij _ => (a ij).ne_zero
  have h := productMeasure_map_diagonal ν.measure complexAbsHom
    (fun z hz => map_complex_mul_addHaar ν.measure hz) hD
  have he : (Matrix.toLin' (Matrix.diagonal D) : (J → ℂ) → (J → ℂ)) =
      fun X ij => D ij * X ij := by
    funext X i
    simp only [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [he, Matrix.det_diagonal, map_prod] at h
  exact h

private theorem integral_scale_upperEntries
    (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure] (a : J → ℂˣ)
    (f : (J → ℂ) → ℂ) (hf : Continuous f) :
    (∫ X : J → ℂ, f (fun ij => (a ij : ℂ) * X ij) ∂upperEntryProductMeasure ν n) =
      ((↑((∏ ij : J, complexAbsHom (a ij : ℂ))⁻¹) : ℝ) : ℂ) *
        ∫ X : J → ℂ, f X ∂upperEntryProductMeasure ν n := by
  let S : (J → ℂ) → J → ℂ := fun X ij => (a ij : ℂ) * X ij
  have hS : Measurable S :=
    (continuous_pi fun ij => continuous_const.mul (continuous_apply ij)).measurable
  change (∫ X, f (S X) ∂upperEntryProductMeasure ν n) = _
  rw [← integral_map hS.aemeasurable hf.aestronglyMeasurable,
    map_scale_upperEntries ν a, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]

/-- Replacing the unipotent factor by the actual strict upper matrix
entries leaves one inverse determinant factor for each row coordinate. -/
theorem integral_diagonal_mul_upperEntries
    (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure] (d : I → ℂˣ)
    (F : M → ℂ) (hF : Continuous F) :
    (∫ X : J → ℂ, F ((diagonalMatrixUnits ℂ d).val *
      ((upperEntryCoordinates n (K := ℂ)).symm X).val.val) ∂upperEntryProductMeasure ν n) =
      ((↑((∏ ij : J, complexAbsHom (d ij.1.1 : ℂ))⁻¹) : ℝ) : ℂ) *
        ∫ X : J → ℂ, F (complexTriangularMatrix (fun i => (d i : ℂ)) X)
          ∂upperEntryProductMeasure ν n := by
  simp_rw [diagonal_mul_upperEntryCoordinates]
  exact integral_scale_upperEntries ν (fun ij => d ij.1.1)
    (F ∘ complexTriangularMatrix (fun i => (d i : ℂ)))
    (hF.comp (continuous_complexTriangularMatrix _))

/-- With the diagonal factor on the right the strict upper entries are
scaled by the column diagonal. -/
theorem integral_upperEntries_mul_diagonal
    (ν : AdditiveHaarMeasure ℂ) [SigmaFinite ν.measure] (d : I → ℂˣ)
    (F : M → ℂ) (hF : Continuous F) :
    (∫ X : J → ℂ, F (((upperEntryCoordinates n (K := ℂ)).symm X).val.val *
      (diagonalMatrixUnits ℂ d).val) ∂upperEntryProductMeasure ν n) =
      ((↑((∏ ij : J, complexAbsHom (d ij.1.2 : ℂ))⁻¹) : ℝ) : ℂ) *
        ∫ X : J → ℂ, F (complexTriangularMatrix (fun i => (d i : ℂ)) X)
          ∂upperEntryProductMeasure ν n := by
  simp_rw [upperEntryCoordinates_mul_diagonal]
  exact integral_scale_upperEntries ν (fun ij => d ij.1.2)
    (F ∘ complexTriangularMatrix (fun i => (d i : ℂ)))
    (hF.comp (continuous_complexTriangularMatrix _))

private def upperEntriesInRow (i : I) : {ij : J // ij.val.1 = i} ≃ Set.Ioi i where
  toFun p := ⟨p.val.val.2, p.property.ge.trans_lt p.val.property⟩
  invFun j := ⟨⟨(i, j.val), j.property⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (Prod.ext p.property.symm rfl)
  right_inv j := Subtype.ext rfl

/-- The additive change of the strict upper entries contributes one copy of
the normalized absolute value for every entry in its row. -/
theorem prod_complexUpperEntryScale (d : I → ℂˣ) :
    ∏ ij : J, complexAbsHom (d ij.1.1 : ℂ) =
      ∏ i : I, complexAbsHom (d i : ℂ) ^ (n - 1 - i.val) := by
  classical
  rw [← Fintype.prod_fiberwise' (fun ij : J => ij.val.1)
    (fun i : I => complexAbsHom (d i : ℂ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr (upperEntriesInRow i),
    Fintype.card_Ioi, Fin.card_Ioi]

private def upperEntriesInColumn (j : I) : {ij : J // ij.val.2 = j} ≃ Set.Iio j where
  toFun p := ⟨p.val.val.1, lt_of_lt_of_eq p.val.property p.property⟩
  invFun i := ⟨⟨(i.val, j), i.property⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (Prod.ext rfl p.property.symm)
  right_inv i := Subtype.ext rfl

theorem prod_complexUpperEntryColumnScale (d : I → ℂˣ) :
    ∏ ij : J, complexAbsHom (d ij.1.2 : ℂ) =
      ∏ j : I, complexAbsHom (d j : ℂ) ^ j.val := by
  classical
  rw [← Fintype.prod_fiberwise' (fun ij : J => ij.val.2)
    (fun j : I => complexAbsHom (d j : ℂ))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr (upperEntriesInColumn j),
    Fintype.card_Iio, Fin.card_Iio]

end Langlands.GodementJacquet
