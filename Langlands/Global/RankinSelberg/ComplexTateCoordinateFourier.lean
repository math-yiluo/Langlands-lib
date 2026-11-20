import Langlands.Analysis.SchwartzPartialFourier
import Langlands.LocalFactor.Archimedean.ComplexTateIdentity

/-! # The positive trace Fourier transform in one complex coordinate -/

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

open Langlands.LocalFactor.ComplexTate (traceChar)

variable {n : ℕ}

local notation "Row" => (Fin n → ℂ)
local notation "RowE" => (PiLp 2 (fun _ : Fin n => ℂ))

private abbrev rowEquiv : RowE ≃L[ℝ] Row := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)

private def splitPi (i : Fin (n + 1)) : (Fin (n + 1) → ℂ) ≃L[ℝ] Row × ℂ :=
  ({ toEquiv := (Fin.insertNthEquiv (fun _ => ℂ) i).symm.trans (Equiv.prodComm _ _)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : _ ≃ₗ[ℝ] _).toContinuousLinearEquiv

private def splitCoordinate (i : Fin (n + 1)) : (Fin (n + 1) → ℂ) ≃L[ℝ] RowE × ℂ :=
  (splitPi i).trans (rowEquiv.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℂ))

@[simp] private theorem splitCoordinate_insertNth (i : Fin (n + 1)) (x : Row) (y : ℂ) :
    splitCoordinate i (i.insertNth y x) = (rowEquiv.symm x, y) := by
  have h : splitPi i (i.insertNth y x) = (x, y) := by
    change ((fun j : Fin n => (i.insertNth y x : Fin (n + 1) → ℂ) (i.succAbove j)),
      (i.insertNth y x : Fin (n + 1) → ℂ) i) = (x, y)
    simp
  simp [splitCoordinate, h]

private theorem hasTemperateGrowth_slice (x : RowE) :
    (fun z : ℂ => (x, z)).HasTemperateGrowth := by
  convert (Function.HasTemperateGrowth.const (E := ℂ) (x, (0 : ℂ))).add
    (ContinuousLinearMap.inr ℝ RowE ℂ).hasTemperateGrowth using 1
  ext z <;> simp

private theorem isometry_slice (x : RowE) : Isometry (fun z : ℂ => (x, z)) := by
  apply Isometry.of_dist_eq
  intro a b
  simp [Prod.dist_eq]

/-- The Schwartz slice obtained by fixing all coordinates except `i`. -/
def coordinateSlice (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (i : Fin (n + 1)) (x : Row) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_slice (rowEquiv.symm x))
    (isometry_slice (rowEquiv.symm x)).antilipschitzWith
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitCoordinate i).symm F)

@[simp] theorem coordinateSlice_apply (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (i : Fin (n + 1))
    (x : Row) (y : ℂ) : coordinateSlice F i x y = F (i.insertNth y x) := by
  change F ((splitCoordinate i).symm (rowEquiv.symm x, y)) = _
  rw [← splitCoordinate_insertNth, ContinuousLinearEquiv.symm_apply_apply]

private def frequency : ℂ ≃L[ℝ] ℂ :=
  ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) (Units.mk0 (-2 : ℂ) (by norm_num))).restrictScalars ℝ).trans
    Complex.conjLIE.toContinuousLinearEquiv

private theorem inner_frequency (x y : ℂ) : inner ℝ x (frequency y) = -2 * (x * y).re := by
  change inner ℝ x (starRingEnd ℂ ((-2 : ℂ) * y)) = _
  rw [Complex.inner, ← map_mul, Complex.conj_re, show (-2 : ℂ) * y * x =
    (((-2 : ℝ)) : ℂ) * (x * y) by push_cast; ring, Complex.re_ofReal_mul]

/-- Positive trace Fourier transformation in coordinate `i`, using twice area in that coordinate. -/
def coordinateFourier (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (i : Fin (n + 1)) : 𝓢(Fin (n + 1) → ℂ, ℂ) :=
  (2 : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((splitCoordinate i).trans ((ContinuousLinearEquiv.refl ℝ _).prodCongr frequency))
    (Langlands.Analysis.SchwartzPartialFourier.transform
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitCoordinate i).symm F))

theorem coordinateFourier_insertNth (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (i : Fin (n + 1))
    (x : Fin n → ℂ) (y : ℂ) : coordinateFourier F i (i.insertNth y x) =
      Langlands.LocalFactor.ComplexTate.fourier (coordinateSlice F i x) y := by
  rw [coordinateFourier, Langlands.LocalFactor.ComplexTate.fourier_apply]
  simp only [smul_apply, smul_eq_mul, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, ContinuousLinearEquiv.trans_apply, splitCoordinate_insertNth,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    Langlands.Analysis.SchwartzPartialFourier.transform_apply]
  rw [Real.fourier_eq', Langlands.LocalFactor.ComplexTate.measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [inner_frequency, coordinateSlice_apply, traceChar]
  rw [← splitCoordinate_insertNth i x z, ContinuousLinearEquiv.symm_apply_apply]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The positive trace transform in any selected coordinate is represented by a Schwartz function,
whose slices are the one-dimensional positive trace transforms. -/
def ComplexTateCoordinateFourierStatement : Prop :=
  ∀ (n : ℕ) (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (i : Fin (n + 1)),
    ∃ H : 𝓢(Fin (n + 1) → ℂ, ℂ), ∀ x y, H (i.insertNth y x) =
      Langlands.LocalFactor.ComplexTate.fourier (coordinateSlice F i x) y

theorem complexTateCoordinateFourier : ComplexTateCoordinateFourierStatement :=
  fun _ F i => ⟨coordinateFourier F i, coordinateFourier_insertNth F i⟩

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
