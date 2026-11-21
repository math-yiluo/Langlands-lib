import Langlands.Global.RankinSelberg.ComplexAdjacentSplitRestriction
import Langlands.Global.RankinSelberg.ComplexGodementFourier
import Langlands.Global.RankinSelberg.ComplexSquareFourierMarginal
import Langlands.Representation.GodementJacquet.ComplexRectangularFourierCovariance

/-! # Square and row Fourier transforms of the split Godement test -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (complexSelfDualMeasure)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry operatorToEntry_apply)
open Langlands.GodementJacquet
open Langlands.HarmonicAnalysis (rectangularFourierIntegral rectangularPairing rowMeasure)
open Langlands.LocalFactor.Archimedean (complexScaledCharacter)
open ComplexGodementColumnProduct (leadingColumns lastColumn columnProduct_apply
  rectangularFourierIntegral_column_mul)
open ComplexSquareFourier (matrixTransform matrixTransform_apply)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {r : ℕ}

local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "columnProd" => ComplexGodementColumnProduct.columnProduct

/-- The positive full Fourier transform in the square variable. -/
def splitSquareTransform (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) (matrixTransform a Φ)

@[simp] theorem splitSquareTransform_apply (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (X : Mat) :
    splitSquareTransform a Φ X = matrixTransform a Φ (-X) := by
  rw [splitSquareTransform, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.neg_apply]

/-- The positive Fourier transform in the row variable as a Schwartz test. -/
def splitRowTransform (a : ℂˣ) (φ : 𝓢(Vec, ℂ)) : 𝓢(Vec, ℂ) :=
  Classical.choose (exists_schwartz_complexCoordinateFourier a φ)

theorem splitRowTransform_apply (a : ℂˣ) (φ : 𝓢(Vec, ℂ)) (y : Vec) :
    splitRowTransform a φ y = splitRowPlus a (complexSelfDualMeasure a) φ y := by
  rw [show splitRowTransform a φ y = complexCoordinateFourier a φ y from
    congrFun (Classical.choose_spec (exists_schwartz_complexCoordinateFourier a φ)) y]
  unfold complexCoordinateFourier splitRowPlus complexCoordinatePair
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  exact congrArg (fun x => φ z * (complexScaledCharacter a).complex x)
    (Finset.sum_congr rfl fun i _ => mul_comm (z i) (y i))

private theorem splitSquare_eq_fourier (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (X : Mat) :
    splitSquareTransform a Φ X =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) Φ X := by
  rw [splitSquareTransform_apply, matrixTransform_apply]
  unfold rectangularFourierIntegral
  refine integral_congr_ae (ae_of_all _ fun (Y : Mat) => ?_)
  have htrace : -Matrix.trace (Matrix.transpose (-X) * Y) = rectangularPairing Y X := by
    simp only [rectangularPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  exact congrArg (fun x => Φ Y * (complexScaledCharacter a).complex x) htrace

private theorem splitRowPlus_inverse (a : ℂˣ) (φ : 𝓢(Vec, ℂ)) (y : Vec) :
    splitRowPlus (-a) (complexSelfDualMeasure a) (splitRowTransform a φ) y = φ y := by
  let κ := Fin (r + 1)
  have hF : (splitRowTransform a φ : Vec → ℂ) = ComplexGodementFourier.fourier a φ := by
    funext x
    exact congrFun (Classical.choose_spec (exists_schwartz_complexCoordinateFourier a φ)) x
  rw [← complexSelfDualMeasure_neg_scale a, ← splitRowTransform_apply]
  have hplus : splitRowTransform (-a) (splitRowTransform a φ) y =
      ComplexGodementFourier.fourier (-a) (splitRowTransform a φ) y :=
    congrFun (Classical.choose_spec (exists_schwartz_complexCoordinateFourier (-a)
      (splitRowTransform a φ))) y
  have hi : Integrable (φ : Vec → ℂ) (ComplexGodementFourier.piMeasure κ a) := by
    change Integrable (φ : Vec → ℂ) (complexCoordinateMeasure κ a)
    exact φ.integrable
  rw [hplus, hF]
  exact ComplexGodementFourier.fourier_neg_fourier a φ.continuous hi
    (integrable_complexCoordinateFourier a φ) y

/-- The transformed split test has the positive square and row factors, and the
reflected partial row transform recovers the original column test. -/
def ComplexAdjacentSplitFourierStatement : Prop :=
  ∀ (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)),
    (operatorToEntry (columnProd (splitSquareTransform a Φ) (splitRowTransform a φ)) : Rect → ℂ) =
      complexRectangularFourier a (operatorToEntry (columnProd Φ φ)) ∧
    ∀ y, splitRowPlus (-a) (complexSelfDualMeasure a) (splitRowTransform a φ) y = φ y

theorem complexAdjacentSplitFourier : ComplexAdjacentSplitFourierStatement (r := r) := by
  intro a Φ φ
  refine ⟨funext fun X => ?_, splitRowPlus_inverse a φ⟩
  rw [operatorToEntry_apply, columnProduct_apply, splitSquare_eq_fourier, splitRowTransform_apply]
  change _ = rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
    (fun Y => Φ (leadingColumns Y) * φ (lastColumn Y)) X
  have : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  have : SigmaFinite (complexSelfDualMeasure a).measure := inferInstance
  rw [rectangularFourierIntegral_column_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  exact congrArg (fun x => φ z * (complexScaledCharacter a).complex x)
    (Finset.sum_congr rfl fun i _ => mul_comm (lastColumn X i) (z i))

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
