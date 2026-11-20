import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz
import Langlands.Representation.GodementJacquet.ComplexMatrixHaar

/-! # Inversion for the self-dual complex trace Fourier integral -/

noncomputable section

open MeasureTheory
open scoped FourierTransform NNReal ENNReal InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.LocalFactor.Archimedean

/-- The unitary positive trace character, viewed as a complex function. -/
abbrev traceCharacter (a : ℂˣ) : ℂ → ℂ := (complexScaledCharacter a).complex

theorem continuous_traceCharacter (a : ℂˣ) : Continuous (traceCharacter a) := by
  change Continuous (fun z : ℂ => ((Real.fourierChar
    (Algebra.trace ℝ ℂ ((a : ℂ) * z)) : Circle) : ℂ))
  simp only [Algebra.trace_complex_apply]
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul continuous_id))))

@[simp]
theorem norm_traceCharacter (a : ℂˣ) (z : ℂ) : ‖traceCharacter a z‖ = 1 :=
  Circle.norm_coe _

@[simp]
theorem traceCharacter_zero (a : ℂˣ) : traceCharacter a 0 = 1 := AddChar.map_zero_eq_one _

theorem traceCharacter_add (a : ℂˣ) (z w : ℂ) :
    traceCharacter a (z + w) = traceCharacter a z * traceCharacter a w :=
  AddChar.map_add_eq_mul _ _ _

theorem traceCharacter_neg_scale (a : ℂˣ) (z : ℂ) :
    traceCharacter (-a) z = traceCharacter a (-z) := by
  change (((Real.fourierChar (Algebra.trace ℝ ℂ ((↑(-a) : ℂ) * z))) : Circle) : ℂ) =
    (((Real.fourierChar (Algebra.trace ℝ ℂ ((a : ℂ) * (-z)))) : Circle) : ℂ)
  simp only [Units.val_neg, neg_mul, mul_neg]

theorem complexSelfDualMeasure_neg_scale (a : ℂˣ) :
    complexSelfDualMeasure (-a) = complexSelfDualMeasure a := by
  simp only [complexSelfDualMeasure, Units.val_neg, nnnorm_neg]

/-- The scalar Fourier integral with the positive complex trace kernel. -/
def complexScalarFourier (a : ℂˣ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ y, f y * traceCharacter a (y * z) ∂(complexSelfDualMeasure a).measure

private def traceFourierScale (a : ℂˣ) : ℝ≥0 := ‖(a : ℂ)‖₊ * 2

private theorem traceFourierScale_ne_zero (a : ℂˣ) : traceFourierScale a ≠ 0 :=
  mul_ne_zero (nnnorm_ne_zero_iff.mpr a.ne_zero) two_ne_zero

private theorem complexSelfDualMeasure_eq (a : ℂˣ) :
    (complexSelfDualMeasure a).measure = traceFourierScale a • (volume : Measure ℂ) :=
  complexScaledMeasure_measure _ _

private def traceFourierCoord (a : ℂˣ) : ℂ ≃L[ℝ] ℂ :=
  (((LinearEquiv.smulOfNeZero ℂ ℂ (2 * (a : ℂ))
    (mul_ne_zero two_ne_zero a.ne_zero)).restrictScalars ℝ).toContinuousLinearEquiv).trans
      Complex.conjCLE

private theorem traceFourierCoord_apply (a : ℂˣ) (z : ℂ) :
    traceFourierCoord a z = starRingEnd ℂ (2 * (a : ℂ) * z) := rfl

private theorem real_inner_traceFourierCoord (a : ℂˣ) (y z : ℂ) :
    ⟪y, traceFourierCoord a z⟫_ℝ = Algebra.trace ℝ ℂ ((a : ℂ) * (y * z)) := by
  rw [Complex.inner, traceFourierCoord_apply, ← map_mul, Complex.conj_re,
    Algebra.trace_complex_apply]
  rw [show 2 * (a : ℂ) * z * y = 2 * ((a : ℂ) * (y * z)) by ring]
  simp [Complex.mul_re]

private theorem map_traceFourierCoord (a : ℂˣ) :
    (volume : Measure ℂ).map (traceFourierCoord a) =
      ((traceFourierScale a) ^ 2)⁻¹ • volume := by
  let b : ℂ := 2 * (a : ℂ)
  have hb : b ≠ 0 := mul_ne_zero two_ne_zero a.ne_zero
  have hm : Measurable (fun z : ℂ => b * z) :=
    (continuous_const.mul continuous_id).measurable
  change (volume : Measure ℂ).map (Complex.conjCLE ∘ (fun z : ℂ => b * z)) = _
  rw [← Measure.map_map Complex.conjCLE.continuous.measurable hm, map_complex_mul_volume hb,
    Measure.map_smul _ Complex.conjCLE.continuous.measurable.aemeasurable,
    show (volume : Measure ℂ).map Complex.conjCLE = volume from
      Complex.conjLIE.measurePreserving.map_eq]
  have ht : ‖(2 : ℂ)‖₊ = (2 : ℝ≥0) := by exact_mod_cast Complex.norm_two
  have he : complexAbsHom b = traceFourierScale a ^ 2 := by
    change ‖(2 : ℂ) * (a : ℂ)‖₊ ^ 2 = (‖(a : ℂ)‖₊ * 2) ^ 2
    rw [nnnorm_mul, ht, mul_comm 2]
  rw [he]

private theorem complexScalarFourier_eq (a : ℂˣ) (f : ℂ → ℂ) (z : ℂ) :
    complexScalarFourier a f z =
      (traceFourierScale a : ℝ) • (𝓕⁻ f) (traceFourierCoord a z) := by
  rw [complexScalarFourier, complexSelfDualMeasure_eq, integral_smul_nnreal_measure,
    NNReal.smul_def, Real.fourierInv_eq]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change f y * traceCharacter a (y * z) = Real.fourierChar ⟪y, traceFourierCoord a z⟫_ℝ • f y
    rw [real_inner_traceFourierCoord, Circle.smul_def, smul_eq_mul, mul_comm]
    rfl

/-- The scalar transform on the Schwartz space realizes the integral pointwise. -/
def complexScalarFourierSchwartz (a : ℂˣ) (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (traceFourierScale a : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceFourierCoord a) (𝓕⁻ f)

@[simp]
theorem complexScalarFourierSchwartz_apply
    (a : ℂˣ) (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    complexScalarFourierSchwartz a f z = complexScalarFourier a f z := by
  simp only [complexScalarFourierSchwartz, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.fourierInv_coe, complexScalarFourier_eq]

/-- Fourier inversion with the self-dual measure for the trace pairing. -/
theorem integral_complexScalarFourier_mul (a : ℂˣ) (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    (∫ y, complexScalarFourier a f y * traceCharacter a (-(y * x))
      ∂(complexSelfDualMeasure a).measure) = f x := by
  let g : ℂ → ℂ := fun w =>
    ((𝓕⁻ (f : ℂ → ℂ)) w) * ((Real.fourierChar (-⟪w, x⟫_ℝ) : Circle) : ℂ)
  let c := traceFourierScale a
  have hphase (y : ℂ) :
      traceCharacter a (-(y * x)) =
        ((Real.fourierChar (-⟪traceFourierCoord a y, x⟫_ℝ) : Circle) : ℂ) := by
    change ((Real.fourierChar (Algebra.trace ℝ ℂ ((a : ℂ) * -(y * x))) : Circle) : ℂ) = _
    rw [mul_neg, map_neg, real_inner_comm, real_inner_traceFourierCoord, mul_comm x y]
  have hfun (y : ℂ) :
      complexScalarFourier a f y * traceCharacter a (-(y * x)) =
        (c : ℂ) * g (traceFourierCoord a y) := by
    rw [complexScalarFourier_eq, Complex.real_smul, hphase]
    simp only [g, c, mul_assoc]
  simp_rw [hfun]
  rw [integral_const_mul]
  have hmap : (∫ y, g (traceFourierCoord a y) ∂(complexSelfDualMeasure a).measure) =
      ∫ w, g w ∂(complexSelfDualMeasure a).measure.map (traceFourierCoord a) :=
    ((traceFourierCoord a).toHomeomorph.measurableEmbedding.integral_map g).symm
  rw [hmap, complexSelfDualMeasure_eq,
    Measure.map_smul _ (traceFourierCoord a).continuous.measurable.aemeasurable,
    map_traceFourierCoord, smul_smul,
    integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  change (c : ℂ) * ((↑↑(c * (c ^ 2)⁻¹) : ℂ) * ∫ w, g w) = _
  have hc : c ≠ 0 := traceFourierScale_ne_zero a
  have hc' : c * (c * (c ^ 2)⁻¹) = 1 := by
    rw [← mul_assoc, ← pow_two, mul_inv_cancel₀ (pow_ne_zero 2 hc)]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul, hc', NNReal.coe_one,
    Complex.ofReal_one, one_mul]
  have hg : (∫ w, g w) = (𝓕 (𝓕⁻ (f : ℂ → ℂ))) x := by
    rw [Real.fourier_eq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by simp [g, Circle.smul_def, mul_comm]
  rw [hg, ← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourier_coe,
    FourierTransform.fourier_fourierInv_eq]

theorem integral_complexScalarFourier_zero (a : ℂˣ) (f : SchwartzMap ℂ ℂ) :
    (∫ y, complexScalarFourier a f y ∂(complexSelfDualMeasure a).measure) = f 0 := by
  simpa using integral_complexScalarFourier_mul a f 0

end Langlands.GodementJacquet
