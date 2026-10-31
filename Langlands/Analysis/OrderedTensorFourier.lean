import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! # Fourier identities for packed ordered Schwartz tensors -/

noncomputable section
open MeasureTheory
open LineDeriv
open scoped BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
set_option autoImplicit false

namespace Langlands.Analysis.OrderedTensorFourier

variable {d r : ℕ}

theorem orderedFrequencyTensor_norm (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖(WithLp.toLp 2 (fun w : Fin r → Fin d =>
      ∏ j : Fin r, (ξ (w j) : ℂ)) : EuclideanSpace ℂ (Fin r → Fin d))‖ = ‖ξ‖ ^ r := by
  apply (sq_eq_sq₀ (norm_nonneg _) (pow_nonneg (norm_nonneg ξ) _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [← Finset.prod_pow, sq_abs]
  rw [← Fintype.sum_pow (fun k : Fin d => (ξ k) ^ 2) r,
    ← EuclideanSpace.real_norm_sq_eq]
  simp only [← pow_mul, Nat.mul_comm 2 r]

def packSchwartz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [Fintype W] [DecidableEq W] (g : W → 𝓢(V, ℂ)) :
    𝓢(V, EuclideanSpace ℂ W) :=
  ∑ w, SchwartzMap.postcompCLM
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single w 1)) (g w)

theorem packSchwartz_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [Fintype W] [DecidableEq W] (g : W → 𝓢(V, ℂ)) (x : V) (w : W) :
    packSchwartz g x w = g w x := by
  simp [packSchwartz, EuclideanSpace.single, Pi.single_apply, mul_ite]

theorem fourier_postcomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : ℂ →L[ℂ] G) (f : 𝓢(V, ℂ)) :
    𝓕 (SchwartzMap.postcompCLM L f) = SchwartzMap.postcompCLM L (𝓕 f) := by
  ext ξ
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • L (f x)) =
    L (∫ x, Real.fourierChar (-inner ℝ x ξ) • f x)
  simpa only [map_smul, Circle.smul_def] using
    L.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr f.integrable)

theorem fourier_packSchwartz {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {W : Type*} [Fintype W] [DecidableEq W] (g : W → 𝓢(V, ℂ)) :
    𝓕 (packSchwartz g) = packSchwartz (fun w => 𝓕 (g w)) := by
  simp only [packSchwartz, FourierTransform.fourier_sum, fourier_postcomp]

theorem eLpNorm_fourier_schwartz {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (f : 𝓢(V, G)) :
    eLpNorm (𝓕 f : 𝓢(V, G)) 2 volume = eLpNorm f 2 volume := by
  apply (ENNReal.toReal_eq_toReal_iff' ((𝓕 f : 𝓢(V, G)).eLpNorm_lt_top 2 volume).ne
    (f.eLpNorm_lt_top 2 volume).ne).mp
  simpa only [← SchwartzMap.norm_toLp] using SchwartzMap.norm_fourier_toL2_eq f

theorem fourier_orderedDeriv
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

end Langlands.Analysis.OrderedTensorFourier
