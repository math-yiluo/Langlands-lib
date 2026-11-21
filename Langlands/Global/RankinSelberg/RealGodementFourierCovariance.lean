import Langlands.Global.RankinSelberg.RealGodementRectangularFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport

/-! # Left-right covariance of the real rectangular Schwartz Fourier transform -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory
open scoped Matrix.Norms.Operator NNReal ENNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {r s : ℕ}

local notation "X" => Matrix (Fin r) (Fin s) ℝ
local notation "G" => Langlands.GeneralLinear r ℝ
local notation "H" => Langlands.GeneralLinear s ℝ

private def leftRightLinearEquiv (A : G) (B : H) : X ≃L[ℝ] X :=
  ({ toEquiv := (rectangularLeftRightHomeomorph A B).toEquiv
     map_add' := fun x y => by
       change A.val * (x + y) * B.val = A.val * x * B.val + A.val * y * B.val
       rw [Matrix.mul_add, Matrix.add_mul]
     map_smul' := fun c x => by
       change A.val * (c • x) * B.val = c • (A.val * x * B.val)
       rw [Matrix.mul_smul, Matrix.smul_mul] } : X ≃ₗ[ℝ] X).toContinuousLinearEquiv

/-- Left-right pullback as a continuous complex-linear map on Schwartz space. -/
def rectangularTranslateCLM (A : G) (B : H) : 𝓢(X, ℂ) →L[ℂ] 𝓢(X, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (leftRightLinearEquiv A B)

/-- Pull back a real rectangular Schwartz function by `X ↦ A X B`. -/
def rectangularTranslate (A : G) (B : H) (Φ : 𝓢(X, ℂ)) : 𝓢(X, ℂ) :=
  rectangularTranslateCLM A B Φ

@[simp] theorem rectangularTranslate_apply (A : G) (B : H) (Φ : 𝓢(X, ℂ)) (x : X) :
    rectangularTranslate A B Φ x = Φ (A.val * x * B.val) := rfl

private theorem realHaar_map_mul (ν : AdditiveHaarMeasure ℝ) (a : ℝ) (ha : a ≠ 0) :
    ν.measure.map (fun x : ℝ => a * x) = (‖a‖₊)⁻¹ • ν.measure := by
  change ν.measure.map (fun x : ℝ => a • x) = _
  rw [Measure.map_addHaar_smul ν.measure ha, Module.finrank_self, pow_one, abs_inv]
  rw [← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

private theorem realRectangularMeasure_map_mul_mul (ν : AdditiveHaarMeasure ℝ) (A : G) (B : H) :
    (Langlands.RankinSelberg.rectangularMeasure ν r s).map (rectangularLeftRightHomeomorph A B) =
      (‖A.val.det‖₊ ^ s * ‖B.val.det‖₊ ^ r)⁻¹ • Langlands.RankinSelberg.rectangularMeasure ν r s := by
  have h := haarMeasure_map_rectangular ν.measure (nnnormHom : ℝ →*₀ ℝ≥0) (realHaar_map_mul ν)
    (Langlands.RankinSelberg.rectangularMeasure ν r s) A.val B.val
    (Matrix.GeneralLinearGroup.det A).ne_zero (Matrix.GeneralLinearGroup.det B).ne_zero
  change (Langlands.RankinSelberg.rectangularMeasure ν r s).map
    (fun Y : X => A.val * Y * B.val) = _
  simpa only [Fintype.card_fin, nnnormHom_apply] using h

/-- Left-right translates are carried to inverse-transpose translates with the
inverse absolute determinant Jacobian in the actual real coordinate measure. -/
def RealGodementFourierCovarianceStatement : Prop :=
  ∀ (r s : ℕ) (a : ℝˣ) (A : Langlands.GeneralLinear r ℝ) (B : Langlands.GeneralLinear s ℝ)
    (Φ : 𝓢(Matrix (Fin r) (Fin s) ℝ, ℂ)) (x : Matrix (Fin r) (Fin s) ℝ),
    realRectangularSchwartzFourier a (rectangularTranslate A B Φ) x =
      (((|A.val.det| ^ s * |B.val.det| ^ r)⁻¹ : ℝ) : ℂ) *
        realRectangularSchwartzFourier a Φ
          ((inverseTranspose r ℝ A).val * x * (inverseTranspose s ℝ B).val)

theorem realGodementFourierCovariance : RealGodementFourierCovarianceStatement := by
  intro r s a A B Φ x
  rw [realRectangularSchwartzFourier_apply, realRectangularSchwartzFourier_apply]
  let ν := realSelfDualMeasure a
  have h := rectangularFourierIntegral_leftRight (realScaledCharacter a) ν A B
    (‖A.val.det‖₊ ^ s * ‖B.val.det‖₊ ^ r)⁻¹ (realRectangularMeasure_map_mul_mul ν A B) Φ x
  have hTranslate : (rectangularTranslate A B Φ : Matrix (Fin r) (Fin s) ℝ → ℂ) =
      fun Y => Φ (A.val * Y * B.val) := funext (rectangularTranslate_apply A B Φ)
  rw [hTranslate]
  simpa only [ν, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs] using h

end Langlands.Global.RankinSelbergGlobal.RealGodement
