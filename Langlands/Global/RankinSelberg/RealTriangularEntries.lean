import Langlands.Global.RankinSelberg.RealSquareFourierMarginal
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-! # Additive entry Jacobians in the full real diagonal coordinates -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.RealSquareFourier (upperTriangularEntries)

variable {n : ℕ}
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "Mat" => Matrix I I ℝ
local notation "U" => upperUnipotent n ℝ
local notation "D" => I → ℝˣ

private theorem continuous_upperTriangularEntries (d : I → ℝ) :
    Continuous (upperTriangularEntries d) := by
  apply continuous_matrix
  intro i j
  by_cases h : i < j
  · simpa only [upperTriangularEntries, h, dite_true] using (continuous_apply (⟨(i,j), h⟩ : J))
  · simp only [upperTriangularEntries, h, dite_false]
    exact continuous_const

theorem realDiagonal_mul_upperEntryCoordinates (d : D) (X : J → ℝ) :
    (diagonalMatrixUnits ℝ d).val * ((upperEntryCoordinates n (K := ℝ)).symm X).val.val =
      upperTriangularEntries (fun i => (d i : ℝ)) (fun ij => (d ij.1.1 : ℝ) * X ij) := by
  let u : U := (upperEntryCoordinates n).symm X
  ext i j
  change (Matrix.diagonal (fun k => (d k : ℝ)) * u.val.val) i j = _
  rw [Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [u, upperEntryCoordinates_symm_upper X hij, upperTriangularEntries, hij, dite_true]
  · rw [u.property.2 _, mul_one]
    simp [upperTriangularEntries]
  · rw [u.property.1 hji, mul_zero]
    simp [upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]

theorem realUpperEntryCoordinates_mul_diagonal (d : D) (X : J → ℝ) :
    ((upperEntryCoordinates n (K := ℝ)).symm X).val.val * (diagonalMatrixUnits ℝ d).val =
      upperTriangularEntries (fun i => (d i : ℝ)) (fun ij => (d ij.1.2 : ℝ) * X ij) := by
  let u : U := (upperEntryCoordinates n).symm X
  ext i j
  change (u.val.val * Matrix.diagonal (fun k => (d k : ℝ))) i j = _
  rw [Matrix.mul_diagonal]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [u, upperEntryCoordinates_symm_upper X hij, upperTriangularEntries, hij, dite_true, mul_comm]
  · rw [u.property.2 _, one_mul]
    simp [upperTriangularEntries]
  · rw [u.property.1 hji, zero_mul]
    simp [upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]

private theorem map_real_mul (ν : AdditiveHaarMeasure ℝ) (a : ℝ) (ha : a ≠ 0) :
    ν.measure.map (fun x => a * x) = (‖a‖₊)⁻¹ • ν.measure := by
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  change ν.measure.map (fun x : ℝ => a • x) = _
  rw [Measure.map_addHaar_smul ν.measure ha, Module.finrank_self, pow_one, abs_inv,
    ← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

private theorem map_scale_realUpperEntries
    (ν : AdditiveHaarMeasure ℝ) [SigmaFinite ν.measure] (a : J → ℝˣ) :
    (upperEntryProductMeasure ν n).map (fun (X : J → ℝ) ij => (a ij : ℝ) * X ij) =
      (∏ ij : J, ‖(a ij : ℝ)‖₊)⁻¹ • upperEntryProductMeasure ν n := by
  let d : J → ℝ := fun ij => a ij
  have hd : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun ij _ => (a ij).ne_zero
  have h := productMeasure_map_diagonal ν.measure (nnnormHom : ℝ →*₀ ℝ≥0) (map_real_mul ν) hd
  have he : (Matrix.toLin' (Matrix.diagonal d) : (J → ℝ) → (J → ℝ)) =
      fun X ij => d ij * X ij := by
    funext X i
    simp only [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [he, Matrix.det_diagonal, map_prod] at h
  exact h

private theorem integral_scale_realUpperEntries {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : AdditiveHaarMeasure ℝ) [SigmaFinite ν.measure] (a : J → ℝˣ)
    (f : (J → ℝ) → E) (hf : Continuous f) :
    (∫ X : J → ℝ, f (fun ij => (a ij : ℝ) * X ij) ∂upperEntryProductMeasure ν n) =
      (↑((∏ ij : J, ‖(a ij : ℝ)‖₊)⁻¹) : ℝ) • ∫ X : J → ℝ, f X ∂upperEntryProductMeasure ν n := by
  let S : (J → ℝ) → J → ℝ := fun X ij => (a ij : ℝ) * X ij
  have hS : Measurable S :=
    (continuous_pi fun ij => continuous_const.mul (continuous_apply ij)).measurable
  change (∫ X, f (S X) ∂upperEntryProductMeasure ν n) = _
  rw [← integral_map hS.aemeasurable hf.aestronglyMeasurable,
    map_scale_realUpperEntries ν a, integral_smul_nnreal_measure]
  rfl

/-- For a diagonal on the left, the additive entries are scaled by the row. -/
theorem integral_realDiagonal_mul_upperEntries {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : AdditiveHaarMeasure ℝ) [SigmaFinite ν.measure] (d : D)
    (F : Mat → E) (hF : Continuous F) :
    (∫ X : J → ℝ, F ((diagonalMatrixUnits ℝ d).val *
      ((upperEntryCoordinates n (K := ℝ)).symm X).val.val) ∂upperEntryProductMeasure ν n) =
      (↑((∏ ij : J, ‖(d ij.1.1 : ℝ)‖₊)⁻¹) : ℝ) •
        ∫ X : J → ℝ, F (upperTriangularEntries (fun i => (d i : ℝ)) X)
          ∂upperEntryProductMeasure ν n := by
  simp_rw [realDiagonal_mul_upperEntryCoordinates]
  exact integral_scale_realUpperEntries ν (fun ij => d ij.1.1)
    (F ∘ upperTriangularEntries (fun i => (d i : ℝ)))
    (hF.comp (continuous_upperTriangularEntries _))

/-- For a diagonal on the right, the additive entries are scaled by the column. -/
theorem integral_realUpperEntries_mul_diagonal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : AdditiveHaarMeasure ℝ) [SigmaFinite ν.measure] (d : D)
    (F : Mat → E) (hF : Continuous F) :
    (∫ X : J → ℝ, F (((upperEntryCoordinates n (K := ℝ)).symm X).val.val *
      (diagonalMatrixUnits ℝ d).val) ∂upperEntryProductMeasure ν n) =
      (↑((∏ ij : J, ‖(d ij.1.2 : ℝ)‖₊)⁻¹) : ℝ) •
        ∫ X : J → ℝ, F (upperTriangularEntries (fun i => (d i : ℝ)) X)
          ∂upperEntryProductMeasure ν n := by
  simp_rw [realUpperEntryCoordinates_mul_diagonal]
  exact integral_scale_realUpperEntries ν (fun ij => d ij.1.2)
    (F ∘ upperTriangularEntries (fun i => (d i : ℝ)))
    (hF.comp (continuous_upperTriangularEntries _))

private def realUpperEntriesInRow (i : I) : {ij : J // ij.val.1 = i} ≃ Set.Ioi i where
  toFun p := ⟨p.val.val.2, p.property.ge.trans_lt p.val.property⟩
  invFun j := ⟨⟨(i, j.val), j.property⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (Prod.ext p.property.symm rfl)
  right_inv j := Subtype.ext rfl

theorem prod_realUpperEntryScale (d : D) :
    ∏ ij : J, ‖(d ij.1.1 : ℝ)‖₊ = ∏ i : I, ‖(d i : ℝ)‖₊ ^ (n - 1 - i.val) := by
  classical
  rw [← Fintype.prod_fiberwise' (fun ij : J => ij.val.1) (fun i : I => ‖(d i : ℝ)‖₊)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr (realUpperEntriesInRow i),
    Fintype.card_Ioi, Fin.card_Ioi]

private def realUpperEntriesInColumn (j : I) : {ij : J // ij.val.2 = j} ≃ Set.Iio j where
  toFun p := ⟨p.val.val.1, lt_of_lt_of_eq p.val.property p.property⟩
  invFun i := ⟨⟨(i.val, j), i.property⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (Prod.ext rfl p.property.symm)
  right_inv i := Subtype.ext rfl

theorem prod_realUpperEntryColumnScale (d : D) :
    ∏ ij : J, ‖(d ij.1.2 : ℝ)‖₊ = ∏ j : I, ‖(d j : ℝ)‖₊ ^ j.val := by
  classical
  rw [← Fintype.prod_fiberwise' (fun ij : J => ij.val.2) (fun j : I => ‖(d j : ℝ)‖₊)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr (realUpperEntriesInColumn i),
    Fintype.card_Iio, Fin.card_Iio]

end Langlands.GodementJacquet
