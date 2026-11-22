import Langlands.Global.RankinSelberg.ComplexGapAlternateHaarDecay
import Langlands.Global.RankinSelberg.ComplexGapTriangularChart
import Langlands.Global.RankinSelberg.ComplexGodementSchwartz
import Langlands.Representation.Derivative.MirabolicDeterminant

/-! # Determinant and Haar weights in the alternate complex chart -/

noncomputable section

open scoped NNReal Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateTailWeights

open Langlands.Archimedean.ComplexMaximalParabolicIntegration (det_upperUnipotent)
open Langlands.GeneralLinear (UpperEntryPair determinant)
open Langlands.GodementJacquet (coe_complexAbsHom complexAbsHom)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGapRightChart (consecutiveTailWeight)
open ComplexGapTailIwasawa (tailModulus)
open ComplexGapTriangularChart (Outer retainedMatrix)
open ComplexGapUpperTail (packedTail)
open ComplexGodement (characterWeight norm_characterWeight)
open ComplexGapAlternateHaarDecay (normalizedDet_logTorus normalizedDet_retained)
open ComplexLocalWhittakerGauge (logTorus)

variable (k q : ℕ)

local notation "J" => Fin (q + 1)
local notation "Tag" => UpperEntryPair (q + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ

private theorem det_insert_tail (p : Outer k q) (Z : N) :
    (retainedMatrix k q p * (packedTail k q 0 Z).val).val.det = (retainedMatrix k q p).val.det := by
  rw [Units.val_mul, Matrix.det_mul, det_upperUnipotent, mul_one]

private theorem mod_eq (y : J → ℝ) :
    (tailModulus y : ℝ) = Real.exp (∑ ij : Tag, 2 * (y ij.val.1 - y ij.val.2)) := by
  rw [tailModulus, NNReal.coe_prod, Real.exp_sum]
  refine Finset.prod_congr rfl fun ij _ => ?_
  change (((complexAbsHom (Real.exp (y ij.val.2 - y ij.val.1) : ℂ))⁻¹ : ℝ≥0) : ℝ) = _
  rw [NNReal.coe_inv, coe_complexAbsHom, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
    ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  norm_num
  ring

private theorem density_eq (y : J → ℝ) :
    (consecutiveTailWeight k q (logTorus y) : ℝ) = Real.exp (-((k : ℝ) * (2 * ∑ j, y j))) := by
  unfold consecutiveTailWeight
  rw [NNReal.coe_inv, NNReal.coe_pow, coe_complexAbsHom]
  change (complexNormalizedAbs (logTorus y).val.det ^ k)⁻¹ = _
  have hDet : complexNormalizedAbs (logTorus y).val.det = Real.exp (2 * ∑ j, y j) :=
    normalizedDet_logTorus y
  rw [hDet, ← Real.exp_nat_mul, ← Real.exp_neg]

private theorem root_sum_le (y : J → ℝ) :
    ∑ ij : Tag, 2 * (y ij.val.1 - y ij.val.2) ≤
      4 * (Fintype.card Tag : ℝ) * (∑ j, |y j|) := by
  have h (j : J) : |y j| ≤ ∑ i, |y i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (y i)) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _ij : Tag, 4 * ∑ j, |y j| := by
      apply Finset.sum_le_sum
      intro ij _
      have hL := (le_abs_self (y ij.val.1)).trans (h _)
      have hR := (neg_le_abs (y ij.val.2)).trans (h _)
      linarith
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The Fourier Jacobian, the adjoining character and both logarithmic Haar
densities have a single exponential majorant in the tail logarithms. -/
def ComplexGapAlternateTailWeightsStatement : Prop :=
  ∀ (d : ComplexCharacterData) (s : ℂ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Outer k q) (Z : N),
    let y := p.1.1.2
    let B := retainedMatrix k q p
    let A := B * (packedTail k q 0 Z).val
    ‖(((complexNormalizedAbs B.val.det)⁻¹ : ℝ) : ℂ) ^ q * characterWeight d s (determinant A)‖ *
      (tailModulus y : ℝ) * (consecutiveTailWeight k q (logTorus y) : ℝ) ≤
      Real.exp (C * ∑ j, |y j|)

theorem complexGapAlternateTailWeights : ComplexGapAlternateTailWeightsStatement k q := by
  intro d s
  let b := (d.exponent + s).re - (q : ℝ) - k
  refine ⟨2 * |b| + 4 * (Fintype.card Tag : ℝ), by positivity, ?_⟩
  intro p Z y B A
  have hDet : complexNormalizedAbs (retainedMatrix k q p).val.det = Real.exp (2 * ∑ j, y j) :=
    normalizedDet_retained p
  have hAbs : 0 ≤ (complexNormalizedAbs B.val.det)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hJac : ‖(((complexNormalizedAbs B.val.det)⁻¹ : ℝ) : ℂ) ^ q‖ =
      Real.exp (-((q : ℝ) * (2 * ∑ j, y j))) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hAbs, hDet,
      ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have hChar : ‖characterWeight d s (determinant A)‖ =
      Real.exp ((d.exponent + s).re * (2 * ∑ j, y j)) := by
    rw [norm_characterWeight]
    change complexNormalizedAbs A.val.det ^ (d.exponent + s).re = _
    rw [det_insert_tail, hDet, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [norm_mul, hJac, hChar, mod_eq, density_eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hRadial : 2 * b * (∑ j, y j) ≤ 2 * |b| * (∑ j, |y j|) := calc
    _ ≤ |2 * b * (∑ j, y j)| := le_abs_self _
    _ = 2 * |b| * |∑ j, y j| := by rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  have hRoot := root_sum_le q y
  dsimp only [b] at hRadial
  linarith

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateTailWeights
