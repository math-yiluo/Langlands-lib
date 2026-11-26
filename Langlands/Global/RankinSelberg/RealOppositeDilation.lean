import Langlands.Global.RankinSelberg.RealModulusOpenCell
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar

/-!
# Diagonal contraction on the real opposite cell

The diagonal with entries `ε^i` contracts the lower simple roots by `ε`.
The transpose of the upper unipotent identifies this action with a diagonal
change of variables in real entry coordinates. We compute its exact
Jacobian and bound the displacement from the identity.
-/

noncomputable section

open MeasureTheory
open scoped Classical ENNReal Matrix.Norms.Elementwise

namespace Langlands.Global.RankinSelbergGlobal.RealOppositeDilation

open Langlands.GeneralLinear (upperUnipotent UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply
  upperEntryProductMeasure)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val diagonalUnits_mul_mul_apply)
open Langlands.RankinSelberg (diagonalConj diagonalConj_val continuous_diagonalConj)
open RealJacquetUnipotentMeasure (entryHaar)
open RealModulusOpenCell (realEntryLebesgue groupTranspose groupTranspose_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ

local instance realOppositeDilationMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance realOppositeDilationBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

private def positiveUnit {ε : ℝ} (hε : 0 < ε) : ℝˣ :=
  Units.mk0 ε hε.ne'

private def diagonalEntries (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Fin n → ℝˣ :=
  fun i => positiveUnit hε ^ i.val

/-- The positive diagonal matrix with `i`-th entry `ε^i`, with indices starting at zero. -/
def contractionDiagonal (n : ℕ) {ε : ℝ} (hε : 0 < ε) : G n :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits (diagonalEntries n hε)

/-- Contraction in the upper-entry model, by the inverse of `contractionDiagonal`. -/
def contraction (n : ℕ) {ε : ℝ} (hε : 0 < ε) : N n ≃* N n :=
  diagonalConj (diagonalEntries n hε)⁻¹

theorem continuous_contraction (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (contraction n hε) :=
  continuous_diagonalConj _

theorem contraction_val {n : ℕ} {ε : ℝ} (hε : 0 < ε) (u : N n) :
    (contraction n hε u).val = (contractionDiagonal n hε)⁻¹ * u.val * contractionDiagonal n hε := by
  simp only [contraction, contractionDiagonal, diagonalConj_val, map_inv, inv_inv]

theorem transpose_contraction {n : ℕ} {ε : ℝ} (hε : 0 < ε) (u : N n) :
    groupTranspose (contraction n hε u).val =
      contractionDiagonal n hε * groupTranspose u.val * (contractionDiagonal n hε)⁻¹ := by
  apply Units.ext
  have hd : (contractionDiagonal n hε).val.transpose = (contractionDiagonal n hε).val := by
    simp [contractionDiagonal]
  have hd' : ((contractionDiagonal n hε)⁻¹).val.transpose = ((contractionDiagonal n hε)⁻¹).val := by
    simp only [contractionDiagonal, ← map_inv, diagonalUnits_val, Matrix.diagonal_transpose]
  simp only [contraction_val, groupTranspose_val, Units.val_mul, Matrix.transpose_mul, hd, hd', mul_assoc]

/-- The exponent of `ε` in the real Jacobian of opposite-unipotent contraction. -/
def contractionDegree (n : ℕ) : ℕ :=
  ∑ ij : UpperEntryPair n, (ij.1.2.val - ij.1.1.val)

theorem contraction_entry {n : ℕ} {ε : ℝ} (hε : 0 < ε) (u : N n) {i j : Fin n} (hij : i < j) :
    (contraction n hε u).val.val i j = (ε ^ (j.val - i.val)) • u.val.val i j := by
  rw [contraction_val, contractionDiagonal, ← map_inv, diagonalUnits_mul_mul_apply]
  simp only [Pi.inv_apply, diagonalEntries, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    positiveUnit, Units.val_mk0, smul_eq_mul]
  have hj : ε ^ j.val = ε ^ i.val * ε ^ (j.val - i.val) := by
    rw [← pow_add, Nat.add_sub_of_le hij.le]
  rw [hj]
  calc
    (ε ^ i.val)⁻¹ * u.val.val i j * (ε ^ i.val * ε ^ (j.val - i.val)) =
      ((ε ^ i.val)⁻¹ * ε ^ i.val) * (ε ^ (j.val - i.val) * u.val.val i j) := by
        ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ hε.ne'), one_mul]

private theorem map_coordinateDilation (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (volume : Measure (UpperEntryPair n → ℝ)).map
        (fun x ij => (ε ^ (ij.1.2.val - ij.1.1.val)) • x ij) =
      ENNReal.ofReal ((ε ^ contractionDegree n)⁻¹) • volume := by
  let p : UpperEntryPair n → ℕ := fun ij => ij.1.2.val - ij.1.1.val
  let f : UpperEntryPair n → ℝ → ℝ := fun ij z => (ε ^ p ij) • z
  let c : UpperEntryPair n → ℝ := fun ij => (ε ^ p ij)⁻¹
  have hc (ij) : 0 < c ij := by dsimp [c]; positivity
  have hf (ij) : Measurable (f ij) := (continuous_id.const_smul (ε ^ p ij)).measurable
  have hmap (ij) : (volume : Measure ℝ).map (f ij) = (c ij).toNNReal • volume := by
    have he : (ε ^ p ij) ^ Module.finrank ℝ ℝ = ε ^ p ij := by
      rw [Module.finrank_self, pow_one]
    change (volume : Measure ℝ).map (fun z => (ε ^ p ij) • z) = _
    rw [Measure.map_addHaar_smul volume (pow_ne_zero _ hε.ne'), he, abs_of_pos (hc ij)]
    exact Measure.coe_nnreal_smul (c ij).toNNReal volume
  have (ij : UpperEntryPair n) : SigmaFinite ((volume : Measure ℝ).map (f ij)) := by
    rw [hmap]
    infer_instance
  have hproduct : ∏ ij, (c ij).toNNReal = ((ε ^ contractionDegree n)⁻¹).toNNReal := by
    rw [← Real.toNNReal_prod_of_nonneg (fun ij _ => (hc ij).le)]
    simp only [c, contractionDegree, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
    rfl
  change (volume : Measure (UpperEntryPair n → ℝ)).map (fun x ij => f ij (x ij)) = _
  rw [volume_pi, Measure.pi_map_pi (fun ij => (hf ij).aemeasurable)]
  simp_rw [hmap]
  rw [HarmonicAnalysis.pi_nnreal_smul, hproduct]
  exact (Measure.coe_nnreal_smul ((ε ^ contractionDegree n)⁻¹).toNNReal _).symm

theorem map_contraction (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (realEntryLebesgue n).map (contraction n hε) =
      ENNReal.ofReal ((ε ^ contractionDegree n)⁻¹) • realEntryLebesgue n := by
  let e := upperEntryCoordinates (K := ℝ) n
  let f : (UpperEntryPair n → ℝ) → (UpperEntryPair n → ℝ) :=
    fun x ij => (ε ^ (ij.1.2.val - ij.1.1.val)) • x ij
  have hf : Measurable f := .of_eval fun ij =>
    ((continuous_apply ij).const_smul (ε ^ (ij.1.2.val - ij.1.1.val))).measurable
  have hcomp : contraction n hε ∘ e.symm = e.symm ∘ f := by
    funext x
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, e.apply_symm_apply]
    funext ij
    rw [show e (contraction n hε (e.symm x)) ij = (contraction n hε (e.symm x)).val.val ij.1.1 ij.1.2
        from upperEntryCoordinates_apply _ _,
      contraction_entry hε _ ij.2]
    have h := congrFun (e.apply_symm_apply x) ij
    simpa only [e, upperEntryCoordinates_apply, f] using congrArg ((ε ^ (ij.1.2.val - ij.1.1.val)) • ·) h
  have hμ : realEntryLebesgue n = (volume : Measure (UpperEntryPair n → ℝ)).map e.symm := by
    rw [volume_pi]
    rfl
  rw [hμ, Measure.map_map (continuous_contraction n hε).measurable e.symm.measurable, hcomp,
    ← Measure.map_map e.symm.measurable hf, map_coordinateDilation n hε,
    Measure.map_smul _ e.symm.measurable.aemeasurable]

/-- The entrywise displacement of a contracted lower-unipotent matrix from the identity. -/
theorem norm_transpose_contraction_sub_one {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hle : ε ≤ 1)
    (u : N n) :
    ‖(groupTranspose (contraction n hε u).val).val - 1‖ ≤
      ε * ‖u.val.val - 1‖ := by
  refine (Matrix.norm_le_iff (mul_nonneg hε.le (norm_nonneg _))).mpr fun i j => ?_
  rw [Matrix.sub_apply, groupTranspose_val, Matrix.transpose_apply]
  rcases lt_trichotomy j i with hji | rfl | hij
  · have hne : i ≠ j := hji.ne'
    rw [Matrix.one_apply_ne hne, sub_zero, contraction_entry hε _ hji,
      norm_smul, Real.norm_of_nonneg (pow_nonneg hε.le _)]
    have hi : j.val < i.val := hji
    have hk : i.val - j.val ≠ 0 := by omega
    have h1 : ε ^ (i.val - j.val) ≤ ε := pow_le_of_le_one hε.le hle hk
    have h2 : ‖u.val.val j i‖ ≤ ‖u.val.val - 1‖ := by
      have h := Matrix.norm_entry_le_entrywise_sup_norm (u.val.val - 1) (i := j) (j := i)
      simpa only [Matrix.sub_apply, Matrix.one_apply_ne hji.ne, sub_zero] using h
    exact mul_le_mul h1 h2 (norm_nonneg _) hε.le
  · rw [Langlands.GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq, sub_self, norm_zero]
    positivity
  · rw [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero _ hij, Matrix.one_apply_ne hij.ne,
      sub_zero, norm_zero]
    positivity

/-- Exact opposite-cell contraction, its Jacobian, and its displacement bound. -/
def RealOppositeDilationStatement : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε),
    (realEntryLebesgue n).map (contraction n hε) =
      ENNReal.ofReal ((ε ^ contractionDegree n)⁻¹) • realEntryLebesgue n ∧
    ∀ u : N n,
      groupTranspose (contraction n hε u).val =
        contractionDiagonal n hε * groupTranspose u.val * (contractionDiagonal n hε)⁻¹ ∧
      (ε ≤ 1 → ‖(groupTranspose (contraction n hε u).val).val - 1‖ ≤ ε * ‖u.val.val - 1‖)

theorem realOppositeDilation : RealOppositeDilationStatement := fun n _ hε =>
  ⟨map_contraction n hε, fun u => ⟨transpose_contraction hε u,
    fun hle => norm_transpose_contraction_sub_one hε hle u⟩⟩

end Langlands.Global.RankinSelbergGlobal.RealOppositeDilation
