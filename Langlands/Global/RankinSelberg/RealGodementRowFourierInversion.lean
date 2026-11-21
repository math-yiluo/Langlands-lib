import Langlands.Global.RankinSelberg.RealGodementFirstColumn
import Langlands.Global.RankinSelberg.RealGodementScaledFourier
import Langlands.Global.RankinSelberg.RealGodementRectangularFourier

/-! # Opposite-sign inversion on the actual real self-dual row measure -/

noncomputable section

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The positive transforms at parameters `a` and `-a` are inverse with the actual
self-dual scale in each coordinate. -/
theorem scaledEuclideanFourier_neg_comp (a : ℝˣ) (Φ : 𝓢(V, ℂ)) :
    scaledEuclideanFourier (-a) (scaledEuclideanFourier a Φ) = Φ := by
  let F : 𝓢(V, ℂ) := 𝓕⁻ Φ
  let c : ℝ := euclideanHaarFactor a V
  have hc : 0 < c := euclideanHaarFactor_pos a V
  have hscale : euclideanHaarFactor (-a) V = c := by
    simp [c, euclideanHaarFactor]
  ext y
  let K : V → ℂ := fun x => Real.fourierChar (-(inner ℝ x y)) • F x
  have hK : (∫ x, K x) = Φ y := by
    change (∫ x, Real.fourierChar (-(inner ℝ x y)) • F x) = _
    rw [← Real.fourier_eq, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  have hchar (x : V) :
      realScaledCharacter (-a) (inner ℝ x y) = Real.fourierChar (-(inner ℝ ((a : ℝ) • x) y)) := by
    simp only [realScaledCharacter_apply, Units.val_neg, real_inner_smul_left, neg_mul]
  have hpoint (x : V) :
      realScaledCharacter (-a) (inner ℝ x y) • scaledEuclideanFourier a Φ x =
        (c : ℂ) * K ((a : ℝ) • x) := by
    rw [hchar, scaledEuclideanFourier_apply, Circle.smul_def, smul_eq_mul]
    change _ * ((c : ℂ) * F _) = _
    rw [mul_left_comm]
    rfl
  rw [scaledEuclideanFourier_eq_integral, euclideanSelfDualMeasure, hscale, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le]
  simp_rw [hpoint, integral_const_mul, Complex.real_smul]
  rw [Measure.integral_comp_smul volume K (a : ℝ), abs_inv, abs_pow, Complex.real_smul, hK,
    ← euclideanHaarFactor_mul_self a V, Complex.ofReal_inv, Complex.ofReal_mul]
  change (c : ℂ) * ((c : ℂ) * (((c : ℂ) * (c : ℂ))⁻¹ * Φ y)) = Φ y
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr hc.ne') (Complex.ofReal_ne_zero.mpr hc.ne')), one_mul]

end Euclidean

section Row

variable (n : ℕ)
local notation "R" => (Fin n → ℝ)
local notation "E" => EuclideanSpace ℝ (Fin n)

private abbrev rowCoordinates : E ≃L[ℝ] R :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

/-- The actual real positive Fourier integral on a row, as a Schwartz test. -/
def realRowSchwartzFourier (a : ℝˣ) (f : 𝓢(R, ℂ)) : 𝓢(R, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rowCoordinates n).symm
    (scaledEuclideanFourier a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rowCoordinates n) f))

/-- Evaluation is the archimedean local row Fourier integral, not a transform with a
separate choice of volume. -/
@[simp] theorem realRowSchwartzFourier_apply (a : ℝˣ) (f : 𝓢(R, ℂ)) (y : R) :
    realRowSchwartzFourier n a f y = realFourierTransform a f y := by
  change scaledEuclideanFourier a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rowCoordinates n) f)
    ((rowCoordinates n).symm y) = _
  rw [scaledEuclideanFourier_eq_integral, realFourierTransform, ArchimedeanLocal.fourierTransform]
  let F : E → ℂ := fun x => realScaledCharacter a (inner ℝ x ((rowCoordinates n).symm y)) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rowCoordinates n) f) x
  rw [← (measurePreserving_columnToEuclidean (m := n) a).integral_comp' F]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change realScaledCharacter a (inner ℝ (WithLp.toLp 2 x : E) (WithLp.toLp 2 y)) • f x = _
  change _ = f x * (realScaledCharacter a).complex (∑ i, x i * y i)
  have h : inner ℝ (WithLp.toLp 2 x : E) (WithLp.toLp 2 y) = ∑ i, x i * y i := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm (y i) (x i)
  rw [h, Circle.smul_def, smul_eq_mul]
  exact mul_comm _ _

/-- Applying the opposite-parameter row transform returns the original Schwartz test. -/
theorem realRowSchwartzFourier_neg_comp (a : ℝˣ) (f : 𝓢(R, ℂ)) :
    realRowSchwartzFourier n (-a) (realRowSchwartzFourier n a f) = f := by
  let A : 𝓢(R, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rowCoordinates n)
  let B : 𝓢(E, ℂ) →L[ℂ] 𝓢(R, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rowCoordinates n).symm
  have h₁ (g : 𝓢(E, ℂ)) : A (B g) = g := by
    ext x
    change g ((rowCoordinates n).symm ((rowCoordinates n) x)) = g x
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have h₂ (g : 𝓢(R, ℂ)) : B (A g) = g := by
    ext x
    change g ((rowCoordinates n) ((rowCoordinates n).symm x)) = g x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  change B (scaledEuclideanFourier (-a) (A (B (scaledEuclideanFourier a (A f))))) = f
  rw [h₁, scaledEuclideanFourier_neg_comp, h₂]

end Row
end Langlands.Global.RankinSelbergGlobal.RealGodement
