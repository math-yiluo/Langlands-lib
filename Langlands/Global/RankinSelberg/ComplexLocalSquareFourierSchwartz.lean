import Langlands.Global.RankinSelberg.ComplexTraceFourier
import Langlands.Global.RankinSelberg.ComplexUnequalJacquetConventionReduction
import Langlands.Representation.GodementJacquet.ComplexTriangularMatchedTests

/-! # The exact positive square Fourier transform on Schwartz space -/

noncomputable section

open Filter MeasureTheory
open Langlands.GodementJacquet Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open scoped FourierTransform Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexTraceFourier

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Idx" => Fin n × Fin n
local notation "Test" => 𝓢(Mat, ℂ)

private def entryCoordinates : Mat ≃L[ℝ] (Idx → ℂ) :=
  ({ toEquiv := (Equiv.curry (Fin n) (Fin n) ℂ).symm
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : _ ≃ₗ[ℝ] _).toContinuousLinearEquiv

variable (n) in
/-- The square matrix Fourier integral with the positive trace character and the
self-dual measure in every entry is a continuous linear operator on Schwartz space. -/
def ComplexLocalSquareFourierSchwartzStatement : Prop :=
  ∀ a : ℂˣ, ∃ T : Test →L[ℂ] Test, ∀ Φ, (T Φ : Mat → ℂ) = complexMatrixFourier a Φ

theorem complexLocalSquareFourierSchwartz : ComplexLocalSquareFourierSchwartzStatement n := by
  intro a
  let E := entryCoordinates (n := n)
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (coordinates.trans E.symm)
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ)
    (E.trans (coordinates.symm.trans (frequency (-a))))
  let T : Test →L[ℂ] Test :=
    ((scale (-a) : ℝ) ^ Fintype.card Idx) • (Q.comp ((FourierTransform.fourierCLM ℂ _).comp P))
  refine ⟨T, fun Φ => funext fun X => ?_⟩
  let H := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm Φ
  have hTX : T Φ X = transform (-a) H (E X) := rfl
  rw [hTX, transform_apply, selfDualMeasure_neg]
  let f (Y : Idx → ℂ) := H Y *
    (complexScaledCharacter (-a)).complex (-∑ p, Y p * E X p)
  have hμ : MeasurePreserving E (complexMatrixAddMeasure n a)
      (Measure.pi (fun _ : Idx => (complexSelfDualMeasure a).measure)) :=
    RectangleTate.measurePreserving_uncurry
      (fun _ : Fin n => fun _ : Fin n => (complexSelfDualMeasure a).measure)
  change (∫ Y, f Y ∂Measure.pi (fun _ : Idx => (complexSelfDualMeasure a).measure)) = _
  rw [← hμ.integral_comp E.toHomeomorph.measurableEmbedding f]
  apply integral_congr_ae
  refine Eventually.of_forall fun Y => ?_
  change Φ (E.symm (E Y)) * (complexScaledCharacter (-a)).complex (-∑ p, E Y p * E X p) =
    Φ Y * (complexScaledCharacter a).complex (rectangularPairing Y X)
  have hp : (∑ p, E Y p * E X p) = rectangularPairing Y X :=
    Fintype.sum_prod_type' (fun (i j : Fin n) => Y i j * X i j)
  rw [E.symm_apply_apply, hp]
  simp only [UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply, Units.val_neg,
    neg_mul, mul_neg, neg_neg]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
