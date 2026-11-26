import Langlands.Global.RankinSelberg.RealDiscreteRankTwoWhittaker
import Langlands.Global.RankinSelberg.RealOrdinaryCharacterTransport
import Langlands.Representation.Archimedean.RealSmallOrthogonalHaar

/-! # Angular dependence of the real rank-two discrete-block coefficients -/

noncomputable section

open Complex Matrix MeasureTheory
open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteRankTwoAngular

open Langlands.Archimedean Langlands.Archimedean.GramFormula Langlands.Archimedean.RealGramFunction
open Langlands.Archimedean.RealStandardNontrivial Langlands.Archimedean.RealBlockRotation
open Langlands.Archimedean.RealSmallOrthogonalHaar Langlands.LocalFactor.Archimedean
open RealDiscreteRankTwoWhittaker RealGodement ArchimedeanLocal RealCharacterChange
open RealLocalWhittaker
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val)

local notation "G" => Langlands.GeneralLinear 2 ℝ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "R" => Unitary.toUnits reflectTwo
local notation "rot" => fun θ => Unitary.toUnits (rotation θ)

/-- The complex unit giving the right rotation eigenvalue in weight one. -/
def angularCharacter (θ : ℝ) : ℂ := (Real.cos θ : ℂ) - I * (Real.sin θ : ℂ)

private theorem gramPoly_rotation (s : Fin 2 → ℂ) (n : ℕ) (g : G) (θ : ℝ) :
    gramFunction s (blockFactor 2 0 n) (g * rot θ) =
      angularCharacter θ ^ n * gramFunction s (blockFactor 2 0 n) g := by
  let k : G := rot θ
  have hk : k ∈ unitaryCompact ℝ 2 := (rotation θ).property
  have hRot : k.val = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := rotation_val θ
  let Y (ij : Fin 2 × Fin 2) := gramEntry (complexify g.val) ij.1 ij.2
  let Z (ij : Fin 2 × Fin 2) := gramEntry (complexify (g.val * k.val)) ij.1 ij.2
  let c : ℂ := Real.cos θ
  let a : ℂ := Real.sin θ
  have h0 (i : Fin 2) : Z (i, 0) = c * Y (i, 0) + a * Y (i, 1) := by
    change gramEntry (complexify (g.val * k.val)) i 0 = _
    rw [gramEntry_mul (mul_transpose_eq_one_of_mem hk), Fin.sum_univ_two, hRot]
    rfl
  have h1 (i : Fin 2) : Z (i, 1) = -a * Y (i, 0) + c * Y (i, 1) := by
    change gramEntry (complexify (g.val * k.val)) i 1 = _
    rw [gramEntry_mul (mul_transpose_eq_one_of_mem hk), Fin.sum_univ_two, hRot]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Complex.ofReal_neg, Y, c, a]
  have hp : MvPolynomial.eval Z (lplus 2 0) = angularCharacter θ * MvPolynomial.eval Y (lplus 2 0) := by
    rw [eval_lplus (by decide : 0 + 1 < 2), eval_lplus (by decide : 0 + 1 < 2)]
    change Z (0, 0) + Z (1, 1) + I * (Z (0, 1) - Z (1, 0)) =
      (c - I * a) * (Y (0, 0) + Y (1, 1) + I * (Y (0, 1) - Y (1, 0)))
    rw [h0, h1, h1, h0]
    linear_combination a * (Y (0, 1) - Y (1, 0)) * I_sq
  have hm : MvPolynomial.eval Z (lminus 2 0) = angularCharacter θ * MvPolynomial.eval Y (lminus 2 0) := by
    rw [eval_lminus (by decide : 0 + 1 < 2), eval_lminus (by decide : 0 + 1 < 2)]
    change Z (1, 1) - Z (0, 0) - I * (Z (0, 1) + Z (1, 0)) =
      (c - I * a) * (Y (1, 1) - Y (0, 0) - I * (Y (0, 1) + Y (1, 0)))
    rw [h1, h0, h1, h0]
    linear_combination -a * (Y (1, 0) + Y (0, 1)) * I_sq
  change gramExpression s (blockFactor 2 0 n) (complexify (g.val * k.val)) = _
  rw [gramFunction, gramExpression_eq, gramExpression_eq, gramFactor_mul (mul_transpose_eq_one_of_mem hk)]
  change gramFactor s (complexify g.val) * MvPolynomial.eval Z (blockFactor 2 0 n) =
    angularCharacter θ ^ n * (gramFactor s (complexify g.val) * MvPolynomial.eval Y (blockFactor 2 0 n))
  rw [eval_blockFactor, eval_blockFactor, hp, hm, mul_pow, mul_pow]
  ring

private theorem discreteCoefficient_rotation (d : ComplexCharacterData) (g : G) (θ : ℝ) :
    discreteCoefficient d (g * rot θ) = angularCharacter θ ^ (d.weight.natAbs + 1) * discreteCoefficient d g := by
  let s := GramFormula.shiftedExponent 2 (realPositionExponent [.induced d])
  let F := gramFunction s (blockFactor 2 0 (d.weight.natAbs + 1))
  have hE : discreteCoefficient d = additiveJacquetIntegral (-1) F := by
    unfold discreteCoefficient
    congr 1
    change gramFunction s (blockPoly 2 [.induced d] 0) = F
    simp [F, blockPoly]
  rw [hE, additiveJacquetIntegral, additiveJacquetIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  unfold additiveJacquetKernel
  dsimp only [F]
  rw [← mul_assoc, gramPoly_rotation]
  ring

private theorem reflection_val : (R : G).val = !![-1, 0; 0, 1] := by
  change (reflectTwo : Mat) = _
  rw [signReflection_val]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]

private theorem reflection_eq_leading : R = leadingCharacterDiagonal 1 1 (-1) := by
  apply Units.ext
  rw [reflection_val, leadingCharacterDiagonal, diagonalUnits_val]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]

private theorem diagonalPoint_mul (a b : ℝˣ) : diagonalPoint (a * b) = diagonalPoint a * diagonalPoint b := by
  simp only [diagonalPoint, map_mul]

private theorem reflection_eq_diagonal : R = diagonalPoint (-1) := by
  apply Units.ext
  rw [reflection_val, diagonalPoint]
  have ht : (Langlands.GodementJacquet.tateScalarEquiv ℝ (-1 : ℝˣ)).val 0 0 = -1 := by
    exact (Matrix.det_fin_one ((Langlands.GodementJacquet.tateScalarEquiv ℝ (-1 : ℝˣ)).val)).symm.trans
      (RealRankZero.det_val_tateScalarEquiv (-1))
  ext i j
  rw [UnequalAnalytic.padGL_apply]
  fin_cases i <;> fin_cases j <;> norm_num [ht, Matrix.one_apply]

private theorem reflection_sq : R * R = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one, reflection_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagonal_reflect (a : ℝˣ) : diagonalPoint a * R = diagonalPoint (-a) := by
  rw [reflection_eq_diagonal, ← diagonalPoint_mul, mul_neg_one]

private theorem reflect_diagonal (a : ℝˣ) : R * diagonalPoint a = diagonalPoint (-a) := by
  rw [reflection_eq_diagonal, ← diagonalPoint_mul, neg_one_mul]

private theorem reflect_rotation (θ : ℝ) : R * rot θ * R = rot (-θ) := by
  simpa only [toUnits_rotation] using signReflection_mul_blockRotation_mul_of_mem (by decide : 0 + 1 < 2)
    (0 : Fin 2) (Or.inl rfl) θ

private theorem rotation_reflect_swap (θ : ℝ) : rot θ * R = R * rot (-θ) := by
  calc
    _ = (R * R) * (rot θ * R) := by rw [reflection_sq, one_mul]
    _ = R * (R * rot θ * R) := by simp only [mul_assoc]
    _ = _ := by rw [reflect_rotation]

private theorem compactRight_mem_model {d : List RealBlock} {a : ℝˣ} {W : G → ℂ} {k : G}
    (hk : k ∈ unitaryCompact ℝ 2) (hW : W ∈ realWhittakerModel 1 d a) :
    ArchimedeanLocal.translateFunction k W ∈ realWhittakerModel 1 d a := by
  let L := Langlands.Whittaker.rightTranslation ℂ G k
  have hle : realWhittakerModel 1 d a ≤ (realWhittakerModel 1 d a).comap L := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    let f' : Langlands.Automorphic.realStandardKFinite 2 d :=
      ⟨L f, rightTranslation_mem_kFiniteFunctions_realStandardModule _ _ f.2 hk⟩
    change L (B f) ∈ realWhittakerModel 1 d a
    rw [← hB.2.2.2.1 ⟨k, hk⟩ f f' rfl]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f', rfl⟩)
  exact hle hW

/-- Conjugating the positive-scale discrete coefficient by the first-coordinate reflection
changes its Whittaker character to the opposite scale. -/
def discreteOppositeCoefficient (d : ComplexCharacterData) (g : G) : ℂ :=
  discreteCoefficient d (R * g * R)

/-- The ordinary discrete-block coefficients at opposite scales have opposite right
angular weights, and the same values on the positive diagonal. -/
def RealDiscreteRankTwoAngularStatement : Prop :=
  ∀ (d : ComplexCharacterData), d.weight ≠ 0 →
    discreteOppositeCoefficient d ∈ realWhittakerModel 1 [.induced d] (-1) ∧
    ∀ (a : ℝˣ) (θ : ℝ),
      discreteCoefficient d (diagonalPoint a * rot θ) =
        angularCharacter θ ^ (d.weight.natAbs + 1) * discreteCoefficient d (diagonalPoint a) ∧
      discreteOppositeCoefficient d (diagonalPoint a * rot θ) =
        angularCharacter (-θ) ^ (d.weight.natAbs + 1) * discreteCoefficient d (diagonalPoint a) ∧
      discreteCoefficient d (diagonalPoint a * rot θ * R) =
        angularCharacter (-θ) ^ (d.weight.natAbs + 1) * discreteCoefficient d (diagonalPoint (-a))

theorem realDiscreteRankTwoAngular : RealDiscreteRankTwoAngularStatement := by
  intro d hd
  refine ⟨?_, fun a θ => ⟨discreteCoefficient_rotation d _ θ, ?_, ?_⟩⟩
  · have hk : R ∈ unitaryCompact ℝ 2 := reflectTwo.property
    have h : leftTranslate R (discreteCoefficient d) ∈ realWhittakerModel 1 [.induced d] (-1) := by
      have hs := leftTranslate_leading_mem_model (r := 1) (q := 1) (a := -1) le_rfl (discreteCoefficient_mem d hd)
      simpa only [← reflection_eq_leading, one_mul] using hs
    have hEq : discreteOppositeCoefficient d =
        ArchimedeanLocal.translateFunction R (leftTranslate R (discreteCoefficient d)) :=
      funext fun g => congrArg (discreteCoefficient d) (mul_assoc R g R)
    rw [hEq]
    exact compactRight_mem_model hk h
  · unfold discreteOppositeCoefficient
    rw [← mul_assoc R, reflect_diagonal, mul_assoc, rotation_reflect_swap, ← mul_assoc, diagonal_reflect, neg_neg]
    exact discreteCoefficient_rotation d _ (-θ)
  · rw [mul_assoc, rotation_reflect_swap, ← mul_assoc, diagonal_reflect]
    exact discreteCoefficient_rotation d _ (-θ)

end Langlands.Global.RankinSelbergGlobal.RealDiscreteRankTwoAngular
