import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Additive upper triangular entries for complex Godement integrals -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)

set_option autoImplicit false

private def upperEntryColumnEquiv (n : ℕ) : UpperEntryPair n ≃ (Σ j : Fin n, Fin j.val) where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv p := Subtype.ext (Prod.ext (Fin.ext rfl) rfl)
  right_inv p := by
    rcases p with ⟨j, i⟩
    rfl

private theorem prod_upperEntry_column {n : ℕ} {A : Type*} [CommMonoid A] (f : Fin n → A) :
    (∏ ij : UpperEntryPair n, f ij.1.2) = ∏ j : Fin n, f j ^ j.val := by
  calc
    _ = ∏ p : (Σ j : Fin n, Fin j.val), f p.1 :=
      Fintype.prod_equiv (upperEntryColumnEquiv n) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.prod_sigma]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The upper triangular matrix with the supplied diagonal and strictly upper entries. -/
def upperTriangularEntries {n : ℕ} (a : Fin n → ℂ) (z : UpperEntryPair n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if hij : i < j then z ⟨(i, j), hij⟩ else if i = j then a i else 0

/-- Multiplication on the right by a positive diagonal scales each strictly upper entry by
its column diagonal. -/
def scaleUpperEntries {n : ℕ} (y : Fin n → ℝ) (x : UpperEntryPair n → ℂ) :
    UpperEntryPair n → ℂ := fun ij => Real.exp (y ij.1.2) • x ij

theorem unipotent_mul_positiveDiagonal_val {n : ℕ}
    (u : Langlands.GeneralLinear.upperUnipotent n ℂ) (y : Fin n → ℝ)
    (a : Fin n → ℂˣ) (ha : ∀ i, (a i : ℂ) = (Real.exp (y i) : ℂ)) :
    (u.val * diagonalUnits a).val = upperTriangularEntries (fun i => (Real.exp (y i) : ℂ))
      (scaleUpperEntries y (upperEntryCoordinates n u)) := by
  ext i j
  rw [Units.val_mul, diagonalUnits_val, Matrix.mul_diagonal, ha]
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [upperTriangularEntries, dite_eq_left hij, scaleUpperEntries, upperEntryCoordinates_apply,
      Complex.real_smul, mul_comm]
  · rw [Langlands.GeneralLinear.UpperUnipotent.entry_diag, one_mul]
    simp [upperTriangularEntries]
  · rw [u.2.1 hji, zero_mul, upperTriangularEntries, dite_eq_right (not_lt_of_gt hji),
      ite_eq_right (ne_of_gt hji)]

private def entryJacobian (y : ℝ) : ℝ≥0 := ⟨(Real.exp y ^ 2)⁻¹, by positivity⟩

/-- The inverse Jacobian of rescaling the strictly upper entries by the positive diagonal. -/
def upperEntryJacobian {n : ℕ} (y : Fin n → ℝ) : ℝ≥0 :=
  ∏ j : Fin n, entryJacobian (y j) ^ j.val

theorem upperEntryJacobian_pos {n : ℕ} (y : Fin n → ℝ) : 0 < upperEntryJacobian y := by
  apply Finset.prod_pos
  intro j _
  apply pow_pos
  exact (show (0 : ℝ) < (Real.exp (y j) ^ 2)⁻¹ by positivity)

theorem upperEntryJacobian_coe {n : ℕ} (y : Fin n → ℝ) :
    (upperEntryJacobian y : ℝ) = ∏ j : Fin n, ((Real.exp (y j) ^ 2)⁻¹) ^ j.val := by
  simp only [upperEntryJacobian, NNReal.coe_prod]
  exact Finset.prod_congr rfl fun j _ => NNReal.coe_pow (entryJacobian (y j)) j.val

/-- Lebesgue measure in the strictly upper entries becomes the column Jacobian times
Lebesgue measure. Each complex entry contributes the inverse square of its column factor. -/
theorem map_scaleUpperEntries {n : ℕ} (y : Fin n → ℝ) :
    (volume : Measure (UpperEntryPair n → ℂ)).map (scaleUpperEntries y) =
      upperEntryJacobian y • (volume : Measure (UpperEntryPair n → ℂ)) := by
  have hmeas (ij : UpperEntryPair n) : Measurable ((Real.exp (y ij.1.2)) • · : ℂ → ℂ) :=
    measurable_const_smul _
  have hscalar (ij : UpperEntryPair n) :
      (volume : Measure ℂ).map ((Real.exp (y ij.1.2)) • ·) =
        entryJacobian (y ij.1.2) • (volume : Measure ℂ) := by
    rw [Measure.map_addHaar_smul volume (Real.exp_ne_zero _), Complex.finrank_real_complex,
      abs_of_pos (by positivity)]
    change ENNReal.ofReal ((Real.exp (y ij.1.2) ^ 2)⁻¹) • (volume : Measure ℂ) =
      (entryJacobian (y ij.1.2) : ℝ≥0∞) • (volume : Measure ℂ)
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  have hσfinite (ij : UpperEntryPair n) :
      SigmaFinite ((volume : Measure ℂ).map ((Real.exp (y ij.1.2)) • ·)) := by
    rw [hscalar]
    infer_instance
  change (Measure.pi (fun _ : UpperEntryPair n => (volume : Measure ℂ))).map
      (fun (x : UpperEntryPair n → ℂ) ij => Real.exp (y ij.1.2) • x ij) =
    upperEntryJacobian y • Measure.pi (fun _ : UpperEntryPair n => (volume : Measure ℂ))
  rw [Measure.pi_map_pi (hμ := hσfinite)
    (fun ij => (hmeas ij).aemeasurable)]
  simp_rw [hscalar]
  rw [Langlands.HarmonicAnalysis.pi_nnreal_smul]
  exact congrArg (fun c : ℝ≥0 => c • (volume : Measure (UpperEntryPair n → ℂ)))
    (prod_upperEntry_column fun j => entryJacobian (y j))

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
