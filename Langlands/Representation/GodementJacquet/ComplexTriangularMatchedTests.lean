import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration
import Langlands.Representation.GodementJacquet.ComplexMatrixFourierMarginal
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport

/-! # Matching complex matrix tests on the diagonal -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Analysis Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.LocalFactor.Archimedean

variable {n : ℕ}
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "M" => Matrix I I ℂ
local notation "D" => I → ℂ
local notation "U" => J → ℂ
local notation "G" => GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n

/-- The additive self-dual measure on square complex matrices. -/
abbrev complexMatrixAddMeasure (n : ℕ) (a : ℂˣ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) n n

local instance matchedTestsScalarHaar (a : ℂˣ) : (complexSelfDualMeasure a).measure.IsAddHaarMeasure :=
  (complexSelfDualMeasure a).isAddHaar

instance complexMatrixAddMeasure_isAddHaar (a : ℂˣ) :
    (complexMatrixAddMeasure n a).IsAddHaarMeasure :=
  RankinSelberg.rectangularMeasure_isAddHaar (complexSelfDualMeasure a) n n

/-- The entrywise Fourier integral for the complex trace character. -/
abbrev complexMatrixFourier (a : ℂˣ) (Φ : M → ℂ) : M → ℂ :=
  rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) Φ

private def matrixRightMul (g : G) : M ≃L[ℝ] M where
  toFun X := X * g.val
  invFun X := X * (g⁻¹).val
  left_inv X := by
    change X * g.val * (g⁻¹).val = X
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv X := by
    change X * (g⁻¹).val * g.val = X
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  map_add' X Y := Matrix.add_mul X Y g.val
  map_smul' c X := Matrix.smul_mul c X g.val
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

/-- The pullback of a matrix Schwartz test by right multiplication by a unitary matrix. -/
def complexMatrixTranslate (k : K) (Φ : SchwartzMap M ℂ) : SchwartzMap M ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (matrixRightMul k.val) Φ

theorem complexMatrixTranslate_apply (k : K) (Φ : SchwartzMap M ℂ) (X : M) :
    complexMatrixTranslate k Φ X = Φ (X * k.val.val) := rfl

/-- The Schwartz test on diagonal coordinates after the strict upper
entries have been integrated out. -/
def complexUpperMarginal (a : ℂˣ) (Φ : SchwartzMap M ℂ) (k : K) : SchwartzMap D ℂ :=
  schwartzBoundedMarginal (complexCoordinateMeasure J a) (fun _ => 1) measurable_const
    (fun _ => le_of_eq norm_one)
    (schwartzSlice (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (complexMatrixCoordinates n).symm (complexMatrixTranslate k Φ)) (0 : U))

@[simp]
theorem complexUpperMarginal_apply (a : ℂˣ) (Φ : SchwartzMap M ℂ) (k : K) (d : D) :
    complexUpperMarginal a Φ k d =
      ∫ X : U, Φ (complexTriangularMatrix d X * k.val.val) ∂complexCoordinateMeasure J a := by
  rw [complexUpperMarginal, schwartzBoundedMarginal_apply]
  simp only [one_mul, schwartzSlice_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, complexMatrixCoordinates_symm_upper, complexMatrixTranslate_apply]

/-- Right multiplication by a unitary matrix preserves the additive measure. -/
theorem measurePreserving_complexMatrixRightMul_unitary (a : ℂˣ) (k : K) :
    MeasurePreserving (fun X : M => X * k.val.val)
      (complexMatrixAddMeasure n a) (complexMatrixAddMeasure n a) := by
  have hdet : complexAbsHom k.val.val.det = 1 := by
    apply NNReal.eq
    change ‖k.val.val.det‖ ^ 2 = 1
    have h := ComplexMaximalParabolicIntegration.normSqC_det_unitary k
    unfold ComplexMaximalParabolicIntegration.normSqC at h
    exact_mod_cast h
  refine ⟨(continuous_id.matrix_mul continuous_const).measurable, ?_⟩
  rw [map_complex_matrix_right, RankinSelberg.GLDeterminantDensity.weight_eq, hdet,
    inv_one, one_pow, one_smul]

/-- Fourier transformation of a unitary translate acts by inverse transpose on the frequency. -/
theorem complexMatrixFourier_translate (a : ℂˣ) (Φ : SchwartzMap M ℂ) (k : K) (X : M) :
    complexMatrixFourier a (complexMatrixTranslate k Φ) X =
      complexMatrixFourier a Φ (X * (inverseTranspose n ℂ k.val).val) := by
  have he : (rectangularLeftRightHomeomorph (1 : G) k.val : M → M) =
      fun Y => Y * k.val.val := by
    funext Y
    simp
  have hm : (complexMatrixAddMeasure n a).map (rectangularLeftRightHomeomorph 1 k.val) =
      (1 : NNReal) • complexMatrixAddMeasure n a := by
    rw [he, (measurePreserving_complexMatrixRightMul_unitary a k).map_eq, one_smul]
  have h := rectangularFourierIntegral_leftRight (complexScaledCharacter a)
    (complexSelfDualMeasure a) 1 k.val 1 hm Φ X
  simpa only [complexMatrixFourier, Units.val_one, Matrix.one_mul, map_one, NNReal.coe_one,
    Complex.ofReal_one, one_mul, ← complexMatrixTranslate_apply k Φ] using h

/-- After unitary translation the lower triangular dual test is precisely
the diagonal Fourier transform of the original upper marginal. -/
theorem integral_complexMatrixFourier_lower_unitary
    (a : ℂˣ) (Φ : SchwartzMap M ℂ) (k : K) (d : D) :
    (∫ X : U, complexMatrixFourier a Φ
      ((complexTriangularMatrix d X).transpose * (inverseTranspose n ℂ k.val).val)
      ∂complexCoordinateMeasure J a) =
      complexCoordinateFourier a (complexUpperMarginal a Φ k) d := by
  simp_rw [← complexMatrixFourier_translate a Φ k]
  change (∫ X : U, rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
    (complexMatrixTranslate k Φ) (complexTriangularMatrix d X).transpose
      ∂complexCoordinateMeasure J a) = _
  rw [integral_rectangularFourierIntegral_lower]
  congr 1
  funext c
  simp only [complexMatrixTranslate_apply, complexUpperMarginal_apply]

end Langlands.GodementJacquet
