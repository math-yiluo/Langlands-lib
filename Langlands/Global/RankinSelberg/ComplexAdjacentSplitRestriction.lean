import Langlands.Global.RankinSelberg.ComplexAdjacentUnfolding
import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Analysis.SchwartzMatrixNorm
import Langlands.HarmonicAnalysis.PartialFourierCovarianceProof

/-! # The continued split Godement integral on the adjacent subgroup -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (complexNormalizedAbs)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry operatorToEntry_apply)
open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open ComplexGodement (characterWeight normPower)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementColumnProduct (columnProduct_apply leadingColumns lastColumn)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementWhittaker (augmentedPoint kernelBase)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "pad" => padGL (Nat.le_succ (r + 1))

private theorem join_mul_pad (X : Mat) (v : Vec) (g : G) :
    rectangularJoin X v * (pad g).val = rectangularJoin (X * g.val) v := by
  have h₁ (i j : Fin (r + 1)) : (pad g).val i.castSucc j.castSucc = g.val i j := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨i.isLt, j.isLt⟩]
    rfl
  have h₂ (i : Fin (r + 1)) : (pad g).val i.castSucc (Fin.last (r + 1)) = 0 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (by simp), Matrix.one_apply_ne (Fin.castSucc_ne_last i)]
  have h₃ (j : Fin (r + 1)) : (pad g).val (Fin.last (r + 1)) j.castSucc = 0 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (by simp),
      Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm]
  have h₄ : (pad g).val (Fin.last (r + 1)) (Fin.last (r + 1)) = 1 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (by simp), Matrix.one_apply_eq]
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [rectangularJoin_mul_apply, rectangularJoin_last, h₂, h₄,
      mul_zero, Finset.sum_const_zero, mul_one, zero_add]
  · rw [rectangularJoin_mul_apply, rectangularJoin_castSucc, Matrix.mul_apply]
    simp only [h₁, h₃, mul_zero, add_zero]

private theorem detPower_eq_normPower {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (s : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs g s = normPower s (determinant g) := by
  have hp : 0 < complexNormalizedAbs g.val.det := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  change Complex.exp (s * (Real.log (complexNormalizedAbs g.val.det) : ℂ)) =
    ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le,
    mul_comm]

private theorem characterWeight_add_detPower {n : ℕ} (g : Langlands.GeneralLinear n ℂ)
    (d : ComplexCharacterData) (t s : ℂ) :
    characterWeight d t (determinant g) * ArchimedeanLocal.detPower complexNormalizedAbs g s =
      characterWeight d (t + s) (determinant g) := by
  change ((d.character (determinant g) : ℂ) * normPower t (determinant g)) *
    ArchimedeanLocal.detPower complexNormalizedAbs g s = (d.character (determinant g) : ℂ) *
      normPower (t + s) (determinant g)
  simp only [← detPower_eq_normPower, ArchimedeanLocal.detPower, add_mul, Complex.exp_add, mul_assoc]

/-- The positive-phase row integral in the partial Fourier transform of a split test. -/
def splitRowPlus (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ) (φ : Vec → ℂ) (y : Vec) : ℂ :=
  ∫ v, φ v * (complexScaledCharacter a).complex (∑ i, y i * v i) ∂rowMeasure μ (r + 1)

private theorem partialFourier_rightTest_columnProduct (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ)
    (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)) (g h : G) :
    partialFourierPlusIntegral (complexScaledCharacter a) μ
      (rightTest (pad g) (operatorToEntry (ComplexGodementColumnProduct.columnProduct Φ φ)))
      (augmentedPoint h) =
      Φ (h * g).val * splitRowPlus a μ φ (Langlands.RankinSelberg.lastRow h⁻¹) := by
  change partialFourierPlusIntegral (complexScaledCharacter a) μ
    (rightTest (pad g) (operatorToEntry (ComplexGodementColumnProduct.columnProduct Φ φ)))
    (rectangularJoin h.val (Langlands.RankinSelberg.lastRow h⁻¹)) = _
  rw [partialFourierPlusIntegral_join, splitRowPlus, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [rightTest_apply, join_mul_pad, operatorToEntry_apply, columnProduct_apply]
  have hleading : leadingColumns (rectangularJoin (h.val * g.val) v) = (h * g).val := by
    ext i j
    exact rectangularJoin_castSucc (h.val * g.val) v i j
  have hlast : lastColumn (rectangularJoin (h.val * g.val) v) = v := by
    funext i
    exact rectangularJoin_last (h.val * g.val) v i
  rw [hleading, hlast, mul_assoc]

/-- On the adjacent padded subgroup, a continued Godement integral with a split
Schwartz test restricts to the convolution kernel for Jacquet's equation (8.3). -/
def ComplexAdjacentSplitRestrictionStatement : Prop :=
  ∀ (ν : Measure G) (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)) (W : G → ℂ) (p : ℂ) (g : G),
    continuedValue ν μ d a (operatorToEntry (ComplexGodementColumnProduct.columnProduct Φ φ)) W (pad g) p =
      (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
        characterWeight d (p + (r : ℂ) / 2 + 1 / 2) (determinant g) *
          ∫ h, Φ (h * g).val * splitRowPlus a μ φ (Langlands.RankinSelberg.lastRow h⁻¹) *
            W h⁻¹ * characterWeight d (p + (r : ℂ) / 2) (determinant h) ∂ν

theorem complexAdjacentSplitRestriction : ComplexAdjacentSplitRestrictionStatement (r := r) := by
  intro ν μ d a Φ φ W p g
  have hdet : determinant (pad g) = determinant g :=
    Units.ext (UnequalAnalytic.det_padGL _ g)
  have ht : (((r + 1 : ℕ) : ℂ) / 2) + p = p + (r : ℂ) / 2 + 1 / 2 := by
    push_cast
    ring
  have hs : ((((r + 1 : ℕ) + 1 : ℂ) / 2) + p) - 1 = p + (r : ℂ) / 2 := by
    push_cast
    ring
  unfold continuedValue
  rw [mul_assoc ((d.character ((-1 : ℂˣ) ^ (r + 1))) : ℂ),
    characterWeight_add_detPower, ht, hdet]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun h => ?_
  rw [iteratedKernel_eq (complexScaledCharacter a) μ d _
    (partialSchwartz a μ (rightTest (pad g) (operatorToEntry (ComplexGodementColumnProduct.columnProduct Φ φ))))
    (partialSchwartz_apply a μ _) W, kernelBase, partialSchwartz_apply,
    partialFourier_rightTest_columnProduct, hs, detPower_eq_normPower]
  simp only [characterWeight, MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
