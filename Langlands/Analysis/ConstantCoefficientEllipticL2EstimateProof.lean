import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement
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

variable {d r : ℕ}

private theorem orderedFrequencyTensor_norm (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖(WithLp.toLp 2 (fun w : Fin r → Fin d =>
      ∏ j : Fin r, (ξ (w j) : ℂ)) : EuclideanSpace ℂ (Fin r → Fin d))‖ = ‖ξ‖ ^ r := by
  apply (sq_eq_sq₀ (norm_nonneg _) (pow_nonneg (norm_nonneg ξ) _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [← Finset.prod_pow, sq_abs]
  rw [← Fintype.sum_pow (fun k : Fin d => (ξ k) ^ 2) r,
    ← EuclideanSpace.real_norm_sq_eq]
  simp only [← pow_mul, Nat.mul_comm 2 r]

private def packSchwartz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [Fintype W] [DecidableEq W] (g : W → 𝓢(V, ℂ)) :
    𝓢(V, EuclideanSpace ℂ W) :=
  ∑ w, SchwartzMap.postcompCLM
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single w 1)) (g w)

private theorem packSchwartz_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [Fintype W] [DecidableEq W] (g : W → 𝓢(V, ℂ)) (x : V) (w : W) :
    packSchwartz g x w = g w x := by
  simp [packSchwartz, EuclideanSpace.single, Pi.single_apply, mul_ite]

private theorem fourier_postcomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : ℂ →L[ℂ] G) (f : 𝓢(V, ℂ)) :
    𝓕 (SchwartzMap.postcompCLM L f) = SchwartzMap.postcompCLM L (𝓕 f) := by
  ext ξ
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • L (f x)) =
    L (∫ x, Real.fourierChar (-inner ℝ x ξ) • f x)
  simpa only [map_smul, Circle.smul_def] using
    L.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr f.integrable)

private theorem fourier_packSchwartz {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {W : Type*} [Fintype W] [DecidableEq W] (g : W → 𝓢(V, ℂ)) :
    𝓕 (packSchwartz g) = packSchwartz (fun w => 𝓕 (g w)) := by
  simp only [packSchwartz, FourierTransform.fourier_sum, fourier_postcomp]

private theorem eLpNorm_fourier_schwartz {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (f : 𝓢(V, G)) :
    eLpNorm (𝓕 f : 𝓢(V, G)) 2 volume = eLpNorm f 2 volume := by
  apply (ENNReal.toReal_eq_toReal_iff' ((𝓕 f : 𝓢(V, G)).eLpNorm_lt_top 2 volume).ne
    (f.eLpNorm_lt_top 2 volume).ne).mp
  simpa only [← SchwartzMap.norm_toLp] using SchwartzMap.norm_fourier_toL2_eq f

private theorem fourier_orderedDeriv
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (w : Fin r → Fin d)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    (𝓕 (∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j)} f) :
      𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ =
      (2 * Real.pi * Complex.I) ^ r *
        (∏ j : Fin r, (ξ (w j) : ℂ)) * (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hg : (inner ℝ · (EuclideanSpace.basisFun (Fin d) ℝ (w 0))).HasTemperateGrowth :=
      ((innerSL ℝ).flip (EuclideanSpace.basisFun (Fin d) ℝ (w 0))).hasTemperateGrowth
    rw [iteratedLineDerivOp_succ_left, SchwartzMap.fourier_lineDerivOp_eq]
    rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
      EuclideanSpace.inner_basisFun_real]
    simp only [RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    change (2 * Real.pi * Complex.I) *
      ((ξ (w 0) : ℂ) *
        (𝓕 (∂^{fun j : Fin r => EuclideanSpace.basisFun (Fin d) ℝ (Fin.tail w j)} f) :
          𝓢(EuclideanSpace ℝ (Fin d), ℂ)) ξ) = _
    rw [ih (Fin.tail w), Fin.prod_univ_succ, pow_succ]
    dsimp [Fin.tail]
    ring

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
