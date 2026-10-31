import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement
import Langlands.Analysis.OrderedTensorFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! # Proof of the scalar constant-coefficient elliptic L² estimate -/

noncomputable section
open MeasureTheory
open LineDeriv
open scoped BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
set_option autoImplicit false

namespace Langlands.Analysis

open OrderedTensorFourier

variable {d r : ℕ}

private theorem schwartzConstantCoefficientEstimate
    (a : (Fin r → Fin d) → ℂ) (c : ℝ) (hc : 0 < c)
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin d),
      c * ‖ξ‖ ^ r ≤ ‖∑ w : Fin r → Fin d, a w * ∏ j : Fin r, (ξ (w j) : ℂ)‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    eLpNorm
        (packSchwartz (fun w : Fin r → Fin d =>
          ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f)) 2 volume ≤
      ENNReal.ofReal c⁻¹ *
        eLpNorm
          ((∑ w : Fin r → Fin d,
            a w • ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f) :
              𝓢(EuclideanSpace ℝ (Fin d), ℂ)) 2 volume := by
  let g (w : Fin r → Fin d) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f
  let T := packSchwartz g
  let P : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := ∑ w, a w • g w
  have hT (ξ : EuclideanSpace ℝ (Fin d)) :
      (𝓕 T : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))) ξ =
        ((2 * Real.pi * Complex.I) ^ r *
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ) •
          (WithLp.toLp 2 (fun w : Fin r → Fin d =>
            ∏ j : Fin r, (ξ (w j) : ℂ)) : EuclideanSpace ℂ (Fin r → Fin d)) := by
    apply PiLp.ext
    intro w
    change (𝓕 (packSchwartz g) :
      𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))) ξ w = _
    rw [fourier_packSchwartz, packSchwartz_apply]
    change (𝓕 (∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f) :
      𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ = _
    rw [fourier_orderedDeriv]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hP (ξ : EuclideanSpace ℝ (Fin d)) :
      (𝓕 P : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ =
        ((2 * Real.pi * Complex.I) ^ r *
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ) *
          (∑ w : Fin r → Fin d, a w * ∏ j : Fin r, (ξ (w j) : ℂ)) := by
    simp only [P, g, FourierTransform.fourier_sum, FourierTransform.fourier_smul,
      sum_apply, smul_apply, smul_eq_mul, fourier_orderedDeriv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hpoint (ξ : EuclideanSpace ℝ (Fin d)) :
      ‖(𝓕 T : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))) ξ‖ ≤
        c⁻¹ * ‖(𝓕 P : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ‖ := by
    have hmul :
        c * ‖(𝓕 T :
          𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))) ξ‖ ≤
          ‖(𝓕 P : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ‖ := by
      rw [hT, hP, norm_smul, orderedFrequencyTensor_norm]
      conv_rhs => rw [norm_mul]
      calc
        c * (‖(2 * Real.pi * Complex.I) ^ r *
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ‖ * ‖ξ‖ ^ r) =
          ‖(2 * Real.pi * Complex.I) ^ r *
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ‖ * (c * ‖ξ‖ ^ r) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hell ξ) (norm_nonneg _)
    calc
      _ = c⁻¹ * (c * ‖(𝓕 T :
          𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))) ξ‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hc.le)
  change eLpNorm T 2 volume ≤ ENNReal.ofReal c⁻¹ * eLpNorm P 2 volume
  rw [← eLpNorm_fourier_schwartz T, ← eLpNorm_fourier_schwartz P]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (𝓕 T : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin r → Fin d))).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hpoint) 2

/-- The homogeneous symbol bound controls the complete ordered derivative tensor. -/
theorem constantCoefficientEllipticL2Estimate :
    ConstantCoefficientEllipticL2EstimateStatement d r := by
  classical
  intro a c hc hell F hsmooth hcompact
  let f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := hcompact.toSchwartzMap hsmooth
  let g (w : Fin r → Fin d) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    ∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f
  let T := packSchwartz g
  let P : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := ∑ w, a w • g w
  have hg (w : Fin r → Fin d) (x : EuclideanSpace ℝ (Fin d)) :
      g w x = iteratedFDeriv ℝ r F x
        (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)) := by
    dsimp [g]
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl
  have hT (x : EuclideanSpace ℝ (Fin d)) :
      ‖T x‖ = Real.sqrt (∑ w : Fin r → Fin d,
        ‖iteratedFDeriv ℝ r F x
          (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j))‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [T, packSchwartz_apply, hg]
  have hP : (P : EuclideanSpace ℝ (Fin d) → ℂ) =
      fun x => ∑ w : Fin r → Fin d, a w * iteratedFDeriv ℝ r F x
        (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)) := by
    funext x
    simp only [P, sum_apply, smul_apply, smul_eq_mul, hg]
  have h := schwartzConstantCoefficientEstimate a c hc hell f
  change eLpNorm T 2 volume ≤ ENNReal.ofReal c⁻¹ * eLpNorm P 2 volume at h
  rw [← eLpNorm_norm T T.continuous.aestronglyMeasurable, hP] at h
  simpa only [hT] using h

end Langlands.Analysis
