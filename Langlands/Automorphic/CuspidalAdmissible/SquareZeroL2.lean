import Langlands.Automorphic.CuspidalL2.UnipotentMeanValue
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Square-mean estimates along square-zero archimedean directions

The squared variation of a smooth function along `s ↦ x (1 + sZ)`, `0 ≤ s ≤ 1`, with
`Z² = 0`, is bounded by the integral over `[0, 1]` of the squared left-invariant derivative
in the direction `Z`. This is the `L²` companion of the Library's mean value estimate
`ArchimedeanGL.norm_sub_le_of_squareZero`.
-/

noncomputable section

universe u

open MeasureTheory
open scoped Classical ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.CuspidalAdmissible

/-- **Jensen for squares.** For a probability measure, `(∫⁻ f)² ≤ ∫⁻ f²`. -/
theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ 2 ≤ ∫⁻ a, f a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  have h2 : ∀ a, f a ^ (2 : ℝ) = f a ^ 2 := fun a => ENNReal.rpow_two (f a)
  simp only [h2] at h
  calc (∫⁻ a, f a ∂μ) ^ 2 ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = ∫⁻ a, f a ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end Langlands.Automorphic.CuspidalAdmissible

namespace Langlands.Global.ArchimedeanGL

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

omit [NumberField K] in
theorem continuous_squareZeroElement_smul {Z : ArchimedeanMatrix K n} (hZ : Z * Z = 0) :
    Continuous fun s : ℝ => squareZeroElement (s • Z) (smul_mul_smul_eq_zero hZ s) := by
  have hunit : Continuous fun s : ℝ =>
      (squareZeroUnit (s • Z) (smul_mul_smul_eq_zero hZ s) : ArchimedeanGL K n) := by
    rw [Units.continuous_iff]
    exact ⟨continuous_const.add (continuous_id.smul continuous_const),
      continuous_const.sub (continuous_id.smul continuous_const)⟩
  exact (archimedeanGLCoordinates K n).symm.continuous.comp hunit

/-- **Square-mean estimate along a square-zero direction.** -/
theorem enorm_sub_sq_le_lintegral_squareZero (f : SmoothFunctions K n)
    (x : InfiniteAdelicGL K n) (Z : RealLieAlgebra K n)
    (hZ : realLieAlgebraToMatrix K n Z * realLieAlgebraToMatrix K n Z = 0) :
    ‖f.val (x * squareZeroElement (realLieAlgebraToMatrix K n Z) hZ) - f.val x‖ₑ ^ 2 ≤
      ∫⁻ s in Set.Icc (0 : ℝ) 1, ‖(smoothDifferential K n Z f).val
        (x * squareZeroElement (s • realLieAlgebraToMatrix K n Z)
          (smul_mul_smul_eq_zero hZ s))‖ₑ ^ 2 := by
  set Zm := realLieAlgebraToMatrix K n Z with hZm
  set xc : ArchimedeanGL K n := archimedeanGLCoordinates K n x with hxc
  let p : ℝ → ArchimedeanMatrix K n := fun s => (xc : ArchimedeanMatrix K n) * (1 + s • Zm)
  let h : ℝ → ℂ := fun s => coordinateExtension K n f (p s)
  let D : ℝ → ℂ := fun s => (smoothDifferential K n Z f).val
    (x * squareZeroElement (s • Zm) (smul_mul_smul_eq_zero hZ s))
  have hp_unit (s : ℝ) : p s =
      ((xc * squareZeroUnit (s • Zm) (smul_mul_smul_eq_zero hZ s) : ArchimedeanGL K n) :
        ArchimedeanMatrix K n) := rfl
  have hh (s : ℝ) : h s = f.val (x * squareZeroElement (s • Zm) (smul_mul_smul_eq_zero hZ s)) := by
    change coordinateExtension K n f (p s) = _
    rw [hp_unit, coordinateExtension_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
    rfl
  have hpderiv (s : ℝ) : HasDerivAt p ((xc : ArchimedeanMatrix K n) * Zm) s := by
    have h1 : HasDerivAt (fun s : ℝ => (1 : ArchimedeanMatrix K n) + s • Zm) Zm s := by
      simpa using ((hasDerivAt_id s).smul_const Zm).const_add (1 : ArchimedeanMatrix K n)
    have h2 := h1.const_mul (xc : ArchimedeanMatrix K n)
    simpa [p] using h2
  have hderiv (s : ℝ) : HasDerivAt h (D s) s := by
    have hdiff : DifferentiableAt ℝ (coordinateExtension K n f) (p s) := by
      rw [hp_unit]
      exact (coordinateExtension_contDiffAt K n f _).differentiableAt (by simp)
    have hc : HasDerivAt h
        (fderiv ℝ (coordinateExtension K n f) (p s) ((xc : ArchimedeanMatrix K n) * Zm)) s :=
      hdiff.hasFDerivAt.comp_hasDerivAt s (hpderiv s)
    refine hc.congr_deriv ?_
    have hco : (archimedeanGLCoordinates K n
        (x * squareZeroElement (s • Zm) (smul_mul_smul_eq_zero hZ s)) : ArchimedeanMatrix K n) =
        p s := by
      rw [hp_unit, map_mul, squareZeroElement, ContinuousMulEquiv.apply_symm_apply]
    change _ = (smoothDifferential K n Z f).val _
    rw [smoothDifferential_apply, hco]
    congr 1
    change (xc : ArchimedeanMatrix K n) * Zm = (xc : ArchimedeanMatrix K n) * (1 + s • Zm) * Zm
    rw [mul_assoc, add_mul, one_mul, smul_mul_assoc, hZ, smul_zero, add_zero]
  have hDc : Continuous D :=
    (ArchimedeanGL.continuous K n (smoothDifferential K n Z f)).comp
      (continuous_const.mul (continuous_squareZeroElement_smul hZ))
  have hftc : h 1 - h 0 = ∫ s in (0 : ℝ)..1, D s :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hDc.intervalIntegrable 0 1)).symm
  have h1 : h 1 = f.val (x * squareZeroElement Zm hZ) := by
    rw [hh]
    simp only [one_smul]
  have h0 : h 0 = f.val x := by
    rw [hh]
    have : squareZeroElement ((0 : ℝ) • Zm) (smul_mul_smul_eq_zero hZ 0) = 1 := by
      apply (archimedeanGLCoordinates K n).injective
      rw [squareZeroElement, ContinuousMulEquiv.apply_symm_apply, map_one]
      apply Units.ext
      simp
    rw [this, mul_one]
  rw [← h1, ← h0, hftc, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  calc ‖∫ s in Set.Icc (0 : ℝ) 1, D s‖ₑ ^ 2
      ≤ (∫⁻ s in Set.Icc (0 : ℝ) 1, ‖D s‖ₑ) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1, ‖D s‖ₑ ^ 2 :=
        Langlands.Automorphic.CuspidalAdmissible.sq_lintegral_le _
          hDc.enorm.aemeasurable

end Langlands.Global.ArchimedeanGL
