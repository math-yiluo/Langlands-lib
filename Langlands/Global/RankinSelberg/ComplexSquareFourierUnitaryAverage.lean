import Langlands.Global.RankinSelberg.ComplexSquareFourierAverage
import Langlands.Representation.Archimedean.ComplexGeneralLinearHaarDensity
import Langlands.Representation.Archimedean.ComplexReverseTwist
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport

/-! # Fourier covariance of compact unitary averages of square Schwartz tests -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareFourier

open ArchimedeanLocal
open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (rectangularMeasure)
open Langlands.RankinSelberg.GLDeterminantDensity (weight_eq)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "K" => unitaryCompact ℂ n

private theorem squareSelfDualMeasure_eq (a : ℂˣ) :
    squareSelfDualMeasure n a = (ComplexTraceFourier.scale a ^ n) ^ n • matrixLebesgue n := by
  change Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => (complexSelfDualMeasure a).measure)) =
    (ComplexTraceFourier.scale a ^ n) ^ n • Measure.pi (fun _ : Fin n => (volume : Measure (Fin n → ℂ)))
  simp only [ComplexTraceFourier.product_measure_eq, Fintype.card_fin,
    Langlands.HarmonicAnalysis.pi_nnreal_smul, Finset.prod_const, Finset.card_univ]

private theorem measurePreserving_unitary_left (a : ℂˣ) (k : K) :
    MeasurePreserving (fun X : Mat => k.val.val * X) (squareSelfDualMeasure n a)
      (squareSelfDualMeasure n a) := by
  have hm : Measurable (fun X : Mat => k.val.val * X) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have h := ComplexMaximalParabolicIntegration.normSqC_det_unitary k
  have hdet : normSqHom k.val.val.det = 1 := by
    apply Subtype.ext
    change ‖k.val.val.det‖ ^ 2 = (1 : ℝ)
    exact Complex.ofReal_injective h
  refine ⟨hm, ?_⟩
  rw [squareSelfDualMeasure_eq, Measure.map_smul _ hm.aemeasurable,
    map_left_volume, weight_eq, hdet, inv_one, one_pow, one_smul]

private theorem measurePreserving_unitary_right (a : ℂˣ) (k : K) :
    MeasurePreserving (fun X : Mat => X * k.val.val) (squareSelfDualMeasure n a)
      (squareSelfDualMeasure n a) := by
  have : SigmaFinite (complexSelfDualMeasure a).measure := by
    rw [ComplexTraceFourier.measure_eq]
    infer_instance
  have ht : MeasurePreserving (Matrix.transpose : Mat → Mat) (squareSelfDualMeasure n a)
      (squareSelfDualMeasure n a) :=
    Langlands.GodementJacquet.measurePreserving_transpose_rectangularMeasure (complexSelfDualMeasure a) n n
  let kT : K := ⟨transposeGL k.val, transposeGL_mem k.2⟩
  have he : (Matrix.transpose : Mat → Mat) ∘ (fun X => kT.val.val * X) ∘ Matrix.transpose =
      fun X => X * k.val.val := by
    funext X
    change (k.val.valᵀ * Xᵀ)ᵀ = X * k.val.val
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [← he]
  exact ht.comp ((measurePreserving_unitary_left a kT).comp ht)

private theorem squareFourierIntegral_eq_rectangular (a : ℂˣ) (f : Mat → ℂ) (X : Mat) :
    squareFourierIntegral a f X =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) f (-X) := by
  have hp (Y : Mat) : rectangularPairing Y (-X) = -Matrix.trace (Xᵀ * Y) := by
    simp only [rectangularPairing, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    congr 1
    rw [Finset.sum_comm]
    simp only [mul_comm]
  simp only [squareFourierIntegral, rectangularFourierIntegral, hp]

private theorem squareFourierIntegral_unitary (a : ℂˣ) (A B : K) (f : Mat → ℂ) (X : Mat) :
    squareFourierIntegral a (fun Y => f (A.val.val * Y * B.val.val)) X =
      squareFourierIntegral a f ((conjK n A).val.val * X * (conjK n B).val.val) := by
  have hp : MeasurePreserving (rectangularLeftRightHomeomorph A.val B.val)
      (squareSelfDualMeasure n a) (squareSelfDualMeasure n a) :=
    (measurePreserving_unitary_right a B).comp (measurePreserving_unitary_left a A)
  have hm : (rectangularMeasure (complexSelfDualMeasure a) n n).map
      (rectangularLeftRightHomeomorph A.val B.val) = (1 : ℝ≥0) • squareSelfDualMeasure n a := by
    rw [one_smul]
    exact hp.map_eq
  have h := rectangularFourierIntegral_leftRight (complexScaledCharacter a) (complexSelfDualMeasure a)
    A.val B.val 1 hm f (-X)
  have hInv (k : K) : inverseTranspose n ℂ k.val = (conjK n k).val := Units.ext rfl
  simp only [squareFourierIntegral_eq_rectangular]
  simpa only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_neg, neg_mul, hInv] using h

/-- Fourier transformation commutes with the compact average of left-right unitary
translates when each translating matrix is replaced by its inverse transpose. -/
def ComplexSquareFourierUnitaryAverageStatement : Prop :=
  ∀ {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (κ : Measure Y) [IsFiniteMeasure κ] (a : ℂˣ) (w : Y → ℂ) (A B : Y → K),
    Continuous w → Continuous A → Continuous B → ∀ (Φ Ψ : 𝓢(Mat, ℂ)),
    (∀ X, Ψ X = ∫ y, w y * Φ ((A y).val.val * X * (B y).val.val) ∂κ) → ∀ X,
      matrixTransform a Ψ X = ∫ y, w y * matrixTransform a Φ
        ((conjK n (A y)).val.val * X * (conjK n (B y)).val.val) ∂κ

theorem complexSquareFourierUnitaryAverage : ComplexSquareFourierUnitaryAverageStatement (n := n) := by
  intro Y _ _ _ _ κ _ a w A B hw hA hB Φ Ψ hΨ X
  let T (y : Y) (X : Mat) := (A y).val.val * X * (B y).val.val
  have hA' : Continuous (fun y : Y => (A y).val.val) :=
    Units.continuous_val.comp (continuous_subtype_val.comp hA)
  have hB' : Continuous (fun y : Y => (B y).val.val) :=
    Units.continuous_val.comp (continuous_subtype_val.comp hB)
  have hT : Continuous (Function.uncurry T) :=
    ((hA'.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hB'.comp continuous_fst)
  have hP (y : Y) : MeasurePreserving (T y) (squareSelfDualMeasure n a) (squareSelfDualMeasure n a) :=
    (measurePreserving_unitary_right a (B y)).comp (measurePreserving_unitary_left a (A y))
  rw [complexSquareFourierAverage κ a w T hw hT hP Φ Ψ hΨ X]
  apply integral_congr_ae
  filter_upwards with y
  change w y * squareFourierIntegral a (fun Z => Φ ((A y).val.val * Z * (B y).val.val)) X = _
  rw [squareFourierIntegral_unitary, matrixTransform_eq_squareFourierIntegral]

end Langlands.Global.RankinSelbergGlobal.ComplexSquareFourier
