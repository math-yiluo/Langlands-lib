import Langlands.Analysis.OrderedTensorL2InterpolationStatement
import Langlands.Analysis.OrderedTensorFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! # Scale-explicit ordered tensor interpolation in L² -/

noncomputable section
open MeasureTheory
open LineDeriv
open scoped BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
set_option autoImplicit false

namespace Langlands.Analysis

open OrderedTensorFourier

variable {d r : ℕ}

private theorem scale_power_interpolation {k r : ℕ} (hkr : k ≤ r)
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    t ^ k ≤ ε ^ (r - k) * t ^ r + ε⁻¹ ^ k := by
  by_cases hsmall : ε * t ≤ 1
  · have hbound : t ≤ ε⁻¹ := by
      apply (mul_le_mul_iff_right₀ hε).mp
      simpa only [mul_inv_cancel₀ hε.ne'] using hsmall
    exact (pow_le_pow_left₀ ht hbound k).trans
      (le_add_of_nonneg_left (mul_nonneg (pow_nonneg hε.le _) (pow_nonneg ht _)))
  · have hlarge : 1 ≤ ε * t := (lt_of_not_ge hsmall).le
    have hp : 1 ≤ (ε * t) ^ (r - k) := one_le_pow₀ hlarge
    calc
      t ^ k = 1 * t ^ k := (one_mul _).symm
      _ ≤ (ε * t) ^ (r - k) * t ^ k :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg ht _)
      _ = ε ^ (r - k) * t ^ r := by
        rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hkr]
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg (inv_nonneg.mpr hε.le) _)

private theorem fourier_orderedTensor_norm (q : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖(𝓕 (packSchwartz (fun w : Fin q → Fin d =>
      ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)) :
      𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin q → Fin d))) ξ‖ =
        (2 * Real.pi * ‖ξ‖) ^ q *
          ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ‖ := by
  have hT :
      (𝓕 (packSchwartz (fun w : Fin q → Fin d =>
        ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)) :
        𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin q → Fin d))) ξ =
      ((2 * Real.pi * Complex.I) ^ q *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ) •
        (WithLp.toLp 2 (fun w : Fin q → Fin d =>
          ∏ j : Fin q, (ξ (w j) : ℂ)) : EuclideanSpace ℂ (Fin q → Fin d)) := by
    apply PiLp.ext
    intro w
    rw [fourier_packSchwartz, packSchwartz_apply, fourier_orderedDeriv]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hconst : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hT, norm_smul, norm_mul, norm_pow, orderedFrequencyTensor_norm, hconst, mul_pow]
  ring

private theorem schwartzOrderedTensorInterpolation (k r : ℕ) (hkr : k ≤ r)
    (ε : ℝ) (hε : 0 < ε) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    eLpNorm
        (packSchwartz (fun w : Fin k → Fin d =>
          ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)) 2 volume ≤
      ENNReal.ofReal (ε ^ (r - k)) *
        eLpNorm
          (packSchwartz (fun w : Fin r → Fin d =>
            ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)) 2 volume +
        ENNReal.ofReal (ε⁻¹ ^ k) * eLpNorm f 2 volume := by
  let Tk := packSchwartz (fun w : Fin k → Fin d =>
    ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)
  let Tr := packSchwartz (fun w : Fin r → Fin d =>
    ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)
  let A : ℝ := ε ^ (r - k)
  let B : ℝ := ε⁻¹ ^ k
  have hA : 0 ≤ A := pow_nonneg hε.le _
  have hB : 0 ≤ B := pow_nonneg (inv_nonneg.mpr hε.le) _
  have hpoint (ξ : EuclideanSpace ℝ (Fin d)) :
      ‖(𝓕 Tk : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin k → Fin d))) ξ‖ ≤
        A * ‖(𝓕 Tr : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))) ξ‖ +
          B * ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ‖ := by
    dsimp only [Tk, Tr]
    rw [fourier_orderedTensor_norm, fourier_orderedTensor_norm]
    have h := mul_le_mul_of_nonneg_right
      (scale_power_interpolation (t := 2 * Real.pi * ‖ξ‖) hkr hε
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (norm_nonneg ξ)))
      (norm_nonneg ((𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ))
    simpa only [mul_add, add_mul, mul_assoc] using h
  change eLpNorm Tk 2 volume ≤ ENNReal.ofReal A * eLpNorm Tr 2 volume +
    ENNReal.ofReal B * eLpNorm f 2 volume
  rw [← eLpNorm_fourier_schwartz Tk, ← eLpNorm_fourier_schwartz Tr,
    ← eLpNorm_fourier_schwartz f]
  calc
    _ ≤ eLpNorm
        (A • (fun ξ => ‖(𝓕 Tr :
          𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))) ξ‖) +
          B • (fun ξ => ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ‖)) 2 volume :=
      eLpNorm_mono_real
        (𝓕 Tk : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin k → Fin d))).continuous.aestronglyMeasurable
        hpoint
    _ ≤ _ := by
      refine (eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)).trans_eq ?_
      rw [eLpNorm_const_smul, eLpNorm_const_smul,
        Real.enorm_eq_ofReal hA, Real.enorm_eq_ofReal hB,
        eLpNorm_norm _ (𝓕 Tr :
          𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))).continuous.aestronglyMeasurable,
        eLpNorm_norm _ (𝓕 f :
          𝓢(EuclideanSpace ℝ (Fin d), ℂ)).continuous.aestronglyMeasurable]

/-- Complete ordered derivative tensors interpolate at every positive scale. -/
theorem orderedTensorL2Interpolation : OrderedTensorL2InterpolationStatement d r := by
  classical
  intro k hkr ε hε F hsmooth hcompact
  let f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := hcompact.toSchwartzMap hsmooth
  let T (q : ℕ) := packSchwartz (fun w : Fin q → Fin d =>
    ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)
  have hT (q : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
      ‖T q x‖ = Real.sqrt (∑ w : Fin q → Fin d,
        ‖iteratedFDeriv ℝ q F x
          (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j))‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [T, packSchwartz_apply, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl
  have h := schwartzOrderedTensorInterpolation k r hkr ε hε f
  change eLpNorm (T k) 2 volume ≤ ENNReal.ofReal (ε ^ (r - k)) *
    eLpNorm (T r) 2 volume + ENNReal.ofReal (ε⁻¹ ^ k) * eLpNorm f 2 volume at h
  rw [← eLpNorm_norm (T k) (T k).continuous.aestronglyMeasurable,
    ← eLpNorm_norm (T r) (T r).continuous.aestronglyMeasurable] at h
  have hf : (f : EuclideanSpace ℝ (Fin d) → ℂ) = F := rfl
  rw [hf] at h
  simpa only [hT] using h

end Langlands.Analysis
