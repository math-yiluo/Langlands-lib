import Langlands.Global.RankinSelberg.ComplexUnequalJacquetConventionReduction
import Langlands.HarmonicAnalysis.RectangularFourier
import Mathlib.MeasureTheory.Constructions.Pi

/-! # The mixed row Fourier signs in the complex equal-rank unfolding -/

noncomputable section

open MeasureTheory
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (rectangularMeasure)
open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

variable {m : ℕ}

local notation "Mat" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ
local notation "Rect" => Matrix (Fin m) (Fin (m + 1)) ℂ
local notation "Row" => Fin (m + 1) → ℂ

/-- The first `m` rows of the square matrix. -/
def complexSquareFirstRows (X : Mat) : Rect := fun i => X i.castSucc

/-- The product test in (8.1) obtained from a rectangle test and the last-row test. -/
def complexSquareProductTest (Φ : Rect → ℂ) (φ : Row → ℂ) (X : Mat) : ℂ :=
  Φ (complexSquareFirstRows X) * φ (X (Fin.last m))

/-- Negate the first `m` rows and fix the last row. -/
def complexSquareNegateFirstRows (Y : Mat) : Mat :=
  Fin.lastCases (Y (Fin.last m)) (fun i => -Y i.castSucc)

private theorem rectangleFourier_neg (a : ℂˣ) (Φ : Rect → ℂ) (Y : Rect) :
    rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure (-a)) Φ Y =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) Φ (-Y) := by
  unfold rectangularFourierIntegral
  rw [selfDualMeasure_neg]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun X => ?_
  have h : rectangularPairing X (-Y) = -rectangularPairing X Y := by
    simp only [rectangularPairing, Matrix.neg_apply, mul_neg, ← Finset.sum_neg_distrib]
  simp only [h, UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply, Units.val_neg,
    neg_mul, mul_neg]

/-- Fourier integration of the square product test splits according to the first
rows and the last row, using the same additive Haar measure on every entry. -/
theorem complexSquareProductFourier (a : ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ)
    (Y : Mat) :
    rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
        (complexSquareProductTest Φ φ) Y =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
        Φ (complexSquareFirstRows Y) * complexFourierTransform a φ (Y (Fin.last m)) := by
  let ν := complexSelfDualMeasure a
  let ψ := complexScaledCharacter a
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let η : Measure Row := Measure.pi (fun _ : Fin (m + 1) => ν.measure)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Row) (Fin.last m)
  have hm : MeasurePreserving e (rectangularMeasure ν (m + 1) (m + 1))
      (η.prod (rectangularMeasure ν m (m + 1))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => η) (Fin.last m)
  have hm' := MeasurePreserving.symm e hm
  let f (x : Row) := φ x * ψ.complex (∑ j, x j * Y (Fin.last m) j)
  let F (X : Rect) := Φ X * ψ.complex (rectangularPairing X (complexSquareFirstRows Y))
  let A (X : Mat) := complexSquareProductTest Φ φ X * ψ.complex (rectangularPairing X Y)
  have hlast (p : Row × Rect) : e.symm p (Fin.last m) = p.1 := by
    simp [e, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv]
  have htop (p : Row × Rect) (i : Fin m) : e.symm p i.castSucc = p.2 i := by
    simpa only [Fin.succAbove_last] using
      (show e.symm p ((Fin.last m).succAbove i) = p.2 i by
        simp [e, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv])
  have htest (p : Row × Rect) : A (e.symm p) = f p.1 * F p.2 := by
    have hrows : complexSquareFirstRows (e.symm p) = p.2 := funext (htop p)
    have hpair : rectangularPairing (e.symm p) Y =
        rectangularPairing p.2 (complexSquareFirstRows Y) + ∑ j, p.1 j * Y (Fin.last m) j := by
      unfold rectangularPairing
      rw [Fin.sum_univ_castSucc]
      simp only [complexSquareFirstRows, htop, hlast]
    simp only [A, complexSquareProductTest, f, F, hpair, hrows, hlast, AddChar.map_add_eq_mul]
    ring
  change (∫ X, A X ∂rectangularMeasure ν (m + 1) (m + 1)) = _
  calc
    _ = ∫ p, A (e.symm p) ∂η.prod (rectangularMeasure ν m (m + 1)) :=
      (hm'.integral_comp e.symm.measurableEmbedding A).symm
    _ = ∫ p, f p.1 * F p.2 ∂η.prod (rectangularMeasure ν m (m + 1)) :=
      integral_congr_ae (Filter.Eventually.of_forall htest)
    _ = (∫ x, f x ∂η) * ∫ X, F X ∂rectangularMeasure ν m (m + 1) := integral_prod_mul _ _
    _ = _ := mul_comm _ _

variable (m) in
/-- The product of the negative-parameter rectangular transform and the
positive-parameter row transform is the positive square transform with the
first rows of its argument negated. -/
def ComplexLocalEqualMixedFourierStatement : Prop :=
  ∀ (a : ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ) (Y : Mat),
    rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure (-a))
        Φ (complexSquareFirstRows Y) * complexFourierTransform a φ (Y (Fin.last m)) =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
        (complexSquareProductTest Φ φ) (complexSquareNegateFirstRows Y)

theorem complexLocalEqualMixedFourier : ComplexLocalEqualMixedFourierStatement m := by
  intro a Φ φ Y
  have htop : complexSquareFirstRows (complexSquareNegateFirstRows Y) =
      -complexSquareFirstRows Y := by
    ext i j
    simp [complexSquareFirstRows, complexSquareNegateFirstRows]
  have hlast : complexSquareNegateFirstRows Y (Fin.last m) = Y (Fin.last m) := by
    simp [complexSquareNegateFirstRows]
  rw [complexSquareProductFourier, htop, hlast, rectangleFourier_neg]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
