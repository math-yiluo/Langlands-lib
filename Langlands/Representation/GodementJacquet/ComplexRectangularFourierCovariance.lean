import Langlands.Representation.GodementJacquet.ComplexFourierPartition
import Langlands.Group.GL.Maps

/-! # Fourier covariance for rectangular complex Schwartz functions -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {m n : ℕ}
local notation "R" => Matrix (Fin m) (Fin n) ℂ
local notation "ι₁" => inverseTranspose m ℂ
local notation "ι₂" => inverseTranspose n ℂ

/-- The real linear change of variables given by two-sided matrix multiplication. -/
def complexRectangularMul (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ) : R ≃L[ℝ] R where
  toFun X := A.val * X * B.val
  invFun X := (A⁻¹).val * X * (B⁻¹).val
  left_inv X := by
    change (A⁻¹).val * (A.val * X * B.val) * (B⁻¹).val = X
    simp only [← Matrix.mul_assoc]
    rw [show (A⁻¹).val * A.val = 1 from A.inv_val, Matrix.one_mul,
      Matrix.mul_assoc, show B.val * (B⁻¹).val = 1 from B.val_inv, Matrix.mul_one]
  right_inv X := by
    change A.val * ((A⁻¹).val * X * (B⁻¹).val) * B.val = X
    simp only [← Matrix.mul_assoc]
    rw [show A.val * (A⁻¹).val = 1 from A.val_inv, Matrix.one_mul,
      Matrix.mul_assoc, show (B⁻¹).val * B.val = 1 from B.inv_val, Matrix.mul_one]
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

@[simp]
theorem complexRectangularMul_apply (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ) (X : R) :
    complexRectangularMul A B X = A.val * X * B.val := rfl

/-- Pull back a rectangular Schwartz function by the two matrix multiplications. -/
def complexRectangularTranslate (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ)
    (Φ : SchwartzMap R ℂ) : SchwartzMap R ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexRectangularMul A B) Φ

@[simp]
theorem complexRectangularTranslate_apply (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ)
    (Φ : SchwartzMap R ℂ) (X : R) :
    complexRectangularTranslate A B Φ X = Φ (A.val * X * B.val) := rfl

/-- The rectangular Fourier integral for the given complex trace character. -/
abbrev complexRectangularFourier (a : ℂˣ) (f : R → ℂ) (Y : R) : ℂ :=
  rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) f Y

/-- Fourier integration preserves the rectangular Schwartz space. -/
theorem exists_schwartz_complexRectangularFourier (a : ℂˣ) (Φ : SchwartzMap R ℂ) :
    ∃ Ψ : SchwartzMap R ℂ, (Ψ : R → ℂ) = complexRectangularFourier a Φ := by
  let e := complexRectangleUncurry m n
  let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Φ
  obtain ⟨g, hg⟩ := exists_schwartz_complexCoordinateFourier a f
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g, ?_⟩
  funext X
  change g (e X) = _
  rw [show g (e X) = complexCoordinateFourier a (Φ ∘ e.symm) (e X) from congrFun hg (e X),
    complexCoordinateFourier_rectangleUncurry, e.symm_apply_apply]

/-- The additive Jacobian for `X ↦ A * X * B` using the complex normalized
absolute value. -/
def complexRectangularJacobian (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ) : ℝ≥0 :=
  complexAbsHom A.val.det ^ n * complexAbsHom B.val.det ^ m

theorem map_complexRectangularMul (a : ℂˣ) (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ) :
    let μ := RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) m n
    μ.map (complexRectangularMul A B) = (complexRectangularJacobian A B)⁻¹ • μ := by
  let ν := complexSelfDualMeasure a
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let μ := RankinSelberg.rectangularMeasure ν m n
  let : μ.IsAddHaarMeasure := RankinSelberg.rectangularMeasure_isAddHaar ν m n
  change μ.map (fun X : R => A.val * X * B.val) = _
  simpa only [complexRectangularJacobian, Fintype.card_fin] using
    haarMeasure_map_rectangular ν.measure complexAbsHom (fun _ hz => map_complex_mul_addHaar ν.measure hz)
      μ A.val B.val (Matrix.GeneralLinearGroup.det_ne_zero A) (Matrix.GeneralLinearGroup.det_ne_zero B)

private theorem rectangularPairing_mul_inverseTranspose
    (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ) (X Y : R) :
    rectangularPairing (A.val * X * B.val) ((ι₁ A).val * Y * (ι₂ B).val) =
      rectangularPairing X Y := by
  have htr (P Q : R) : rectangularPairing P Q = Matrix.trace (P * Q.transpose) := rfl
  rw [htr, htr]
  simp only [inverseTranspose_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc Matrix.trace (A.val * X * B.val * ((B⁻¹).val * (Y.transpose * (A⁻¹).val)))
      = Matrix.trace (A.val * (X * Y.transpose * (A⁻¹).val)) := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc B.val, show B.val * (B⁻¹).val = 1 from B.val_inv, Matrix.one_mul]
    _ = Matrix.trace (X * Y.transpose * (A⁻¹).val * A.val) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (X * Y.transpose) := by
      rw [Matrix.mul_assoc, show (A⁻¹).val * A.val = 1 from A.inv_val, Matrix.mul_one]

/-- Fourier transform takes two-sided translations to inverse-transposed
translations with the reciprocal additive Jacobian. -/
theorem complexRectangularFourier_translate (a : ℂˣ)
    (A : GeneralLinear m ℂ) (B : GeneralLinear n ℂ) (Φ : SchwartzMap R ℂ) (Y : R) :
    complexRectangularFourier a (complexRectangularTranslate A B Φ) Y =
      ((complexRectangularJacobian A B)⁻¹ : ℝ≥0) *
        complexRectangularFourier a Φ ((ι₁ A).val * Y * (ι₂ B).val) := by
  let μ := RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) m n
  let e := complexRectangularMul A B
  let F (X : R) := Φ X * traceCharacter a (rectangularPairing X ((ι₁ A).val * Y * (ι₂ B).val))
  change (∫ X : R, complexRectangularTranslate A B Φ X *
    traceCharacter a (rectangularPairing X Y) ∂μ) =
    ((complexRectangularJacobian A B)⁻¹ : ℝ≥0) * ∫ X, F X ∂μ
  calc
    _ = ∫ X, F (e X) ∂μ := by simp only [F, e, complexRectangularMul_apply,
      complexRectangularTranslate_apply, rectangularPairing_mul_inverseTranspose]
    _ = ∫ X, F X ∂μ.map e := (integral_map_equiv e.toHomeomorph.toMeasurableEquiv F).symm
    _ = _ := by
      rw [map_complexRectangularMul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/-- The continuous linear action of an invertible complex matrix on a column. -/
def complexColumnMul (A : GeneralLinear m ℂ) : (Fin m → ℂ) ≃L[ℂ] (Fin m → ℂ) :=
  (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem complexColumnMul_apply (A : GeneralLinear m ℂ) (z : Fin m → ℂ) :
    complexColumnMul A z = A.val.mulVec z :=
  Matrix.GeneralLinearGroup.toLin_apply A z

theorem map_complexColumnMul (a : ℂˣ) (A : GeneralLinear m ℂ) :
    (complexCoordinateMeasure (Fin m) a).map (complexColumnMul A) =
      (complexAbsHom A.val.det)⁻¹ • complexCoordinateMeasure (Fin m) a := by
  let ν := (complexSelfDualMeasure a).measure
  let : ν.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  change (complexCoordinateMeasure (Fin m) a).map (fun z => complexColumnMul A z) = _
  simp only [complexColumnMul_apply]
  exact productMeasure_map_matrix ν complexAbsHom
    (fun _ hz => map_complex_mul_addHaar ν hz) (Matrix.GeneralLinearGroup.det_ne_zero A)

theorem rectangularJoin_left_mul (A X : Matrix (Fin m) (Fin m) ℂ) (z : Fin m → ℂ) :
    rectangularJoin (A * X) (A.mulVec z) = A * rectangularJoin X z := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [rectangularJoin_last, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  · simp only [rectangularJoin_castSucc, Matrix.mul_apply]

end Langlands.GodementJacquet
