import Langlands.Representation.Archimedean.OrthogonalConvolutionDegree
import Langlands.Representation.Archimedean.OrthogonalPolynomialPeakMoment

/-! # Approximation by normalized orthogonal polynomial kernels -/

noncomputable section

open MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.OrthogonalFinitePolynomial

open OrthogonalHaar RealKTypeCount

variable {n : ℕ}

local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

private theorem norm_sub_one_le_distSq_sqrt (x : O n) :
    ‖(x : M n) - 1‖ ≤ (n : ℝ) * Real.sqrt (distSq x 1) := by
  let d := Real.sqrt (distSq x 1)
  let D : ℝ≥0 := ⟨(n : ℝ) * d, by positivity⟩
  change ‖(x : M n) - 1‖ ≤ (D : ℝ)
  rw [Matrix.linfty_opNorm_def]
  refine NNReal.coe_le_coe.mpr (Finset.sup_le fun i _ => NNReal.coe_le_coe.mp ?_)
  rw [NNReal.coe_sum]
  change ∑ j : Fin n, ‖((x : M n) - 1) i j‖ ≤ (n : ℝ) * d
  calc
    _ ≤ ∑ _j : Fin n, d := by
      refine Finset.sum_le_sum fun j _ => ?_
      let A := (x : M n) - 1
      have hij : (A i j) ^ 2 ≤ distSq x 1 := by
        rw [distSq_eq_sum]
        have h₁ : (A i j) ^ 2 ≤ ∑ i', (A i' j) ^ 2 :=
          Finset.single_le_sum (f := fun k : Fin n => (A k j) ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
        have h₂ : ∑ i', (A i' j) ^ 2 ≤ ∑ j', ∑ i', (A i' j') ^ 2 :=
          Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, (A l k) ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
        exact h₁.trans h₂
      simpa only [Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using Real.sqrt_le_sqrt hij
    _ = _ := by simp

private theorem trace_conj_inv (x y : O n) :
    Matrix.trace (↑(x * (x * y)⁻¹) : M n) = Matrix.trace (y : M n) := by
  rw [mul_inv_rev, Submonoid.coe_mul, Submonoid.coe_mul, ← mul_assoc, Matrix.trace_mul_comm,
    ← mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, one_mul]
  change Matrix.trace (star (y : M n)) = _
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.trace_transpose]

private def peak (B : ℝ) : C(O n, ℂ) :=
  (algebraMap ℂ C(O n, ℂ) ((1 - (n : ℝ) / B : ℝ) : ℂ)) +
    ((B : ℂ)⁻¹) • ∑ i : Fin n, entry n (i, i)

private theorem peak_apply {B : ℝ} (hB : B ≠ 0) (x : O n) :
    peak B x = ((polynomialPeak B x : ℝ) : ℂ) := by
  unfold peak polynomialPeak
  rw [distSq_one_eq_trace]
  simp only [ContinuousMap.add_apply, algebraMap_apply, ContinuousMap.smul_apply,
    smul_eq_mul, mul_one, ContinuousMap.sum_apply, entry_apply, ← Complex.ofReal_sum,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply]
  field_simp
  ring

private theorem peak_polynomial (B : ℝ) : peak (n := n) B ∈ polynomialStar n := by
  unfold peak
  exact add_mem ((polynomialStar n).algebraMap_mem _)
    (Submodule.smul_mem (polynomialStar n).toSubmodule _
      (Submodule.sum_mem _ fun i _ => StarAlgebra.subset_adjoin ℂ _ ⟨(i, i), rfl⟩))

private theorem peak_linear (B : ℝ) : (peak (n := n) B : O n → ℂ) ∈ linearSpan n := by
  let P : C(O n, ℂ) →ₗ[ℂ] (O n → ℂ) := ContinuousMap.coeFnLinearMap ℂ
  change P (peak B) ∈ linearSpan n
  unfold peak
  rw [map_add, map_smul, map_sum]
  apply Submodule.add_mem
  · rw [Algebra.algebraMap_eq_smul_one, map_smul, show P 1 = 1 from rfl]
    exact Submodule.smul_mem _ _ (one_le_linearSpan (Submodule.one_le.mp le_rfl))
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => entry_mem_linearSpan (i, i))

/-- Normalized polynomial peaks yield finite-degree central averages with a Lipschitz
approximation error bounded by a constant times `1/t`. -/
def OrthogonalNormalizedPeaksStatement : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (O n)] [BorelSpace (O n)] [MeasurableMul (O n)]
    (μ : Measure (O n)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant],
    0 < n → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 0 < t →
      ∃ w : polynomialStar n,
        w.val ∈ continuousDegree n (t ^ 4) ∧
        (∀ (u : C(O n, ℂ)) (x : O n),
          leftConvolution μ w.val u x = ∫ k, w.val k * u (x * k) ∂μ) ∧
        ∀ (u : C(O n, ℂ)) (L : ℝ), 0 ≤ L →
          (∀ x y : O n, ‖u y - u x‖ ≤ L * ‖(y : M n) - (x : M n)‖) →
          ‖leftConvolution μ w.val u - u‖ ≤ (C / (t : ℝ)) * L

set_option maxHeartbeats 800000 in
theorem orthogonalNormalizedPeaks : OrthogonalNormalizedPeaksStatement := by
  intro n _ _ _ μ _ _ _ hn
  obtain ⟨B, hB, hBn, hBnd⟩ := exists_polynomialPeak_parameter n
  obtain ⟨A, hA, hmoment⟩ := orthogonalPolynomialPeakMoment n μ B hn hB hBn hBnd
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_subtype_val (p := fun x : M n => x ∈ Matrix.unitaryGroup (Fin n) ℝ)).continuousOn
  have hK₀ : 0 ≤ K := (norm_nonneg (1 : M n)).trans (hK (1 : O n) (mem_univ _))
  refine ⟨K * n * A, by positivity, fun t ht => ?_⟩
  let q (x : O n) := polynomialPeak B x ^ (t ^ 4)
  let Z := ∫ x, q x ∂μ
  obtain ⟨hZ, hM⟩ := hmoment t ht
  have hZ' : 0 < Z := hZ
  let w : C(O n, ℂ) := ((Z : ℂ)⁻¹) • (peak B) ^ (t ^ 4)
  have hw (x : O n) : w x = ((q x / Z : ℝ) : ℂ) := by
    simp only [w, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.pow_apply,
      peak_apply hB.ne', q]
    rw [Complex.ofReal_div, Complex.ofReal_pow, div_eq_mul_inv, mul_comm]
  have hwPoly : w ∈ polynomialStar n := (polynomialStar n).toSubmodule.smul_mem _
    (pow_mem (peak_polynomial B) _)
  have hwDegree : w ∈ continuousDegree n (t ^ 4) := by
    apply mem_continuousDegree.mpr
    change (((Z : ℂ)⁻¹) • (peak B : O n → ℂ) ^ (t ^ 4)) ∈ (linearSpan n) ^ (t ^ 4)
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ (peak_linear B) _)
  have hkernel (x y : O n) : w (x * (x * y)⁻¹) = w y := by
    rw [hw, hw]
    simp only [q, polynomialPeak, distSq_one_eq_trace, trace_conj_inv]
  have hright (u : C(O n, ℂ)) (x : O n) :
      leftConvolution μ w u x = ∫ k, w k * u (x * k) ∂μ := by
    rw [leftConvolution_apply_kernel, ← integral_mul_left_eq_self
      (fun k => u k * w (x * k⁻¹)) x]
    simp only [hkernel, mul_comm]
  refine ⟨⟨w, hwPoly⟩, hwDegree, hright, fun u L hL hLip => ?_⟩
  have hC : 0 ≤ (K * (n : ℝ) * A / (t : ℝ)) * L := by positivity
  apply (ContinuousMap.norm_le _ hC).mpr
  intro x
  have hI : (∫ y, w y ∂μ) = 1 := by
    simp_rw [hw]
    rw [integral_complex_ofReal, integral_div]
    change ((Z / Z : ℝ) : ℂ) = _
    simp [hZ'.ne']
  have hJ : (∫ y, w y * u x ∂μ) = u x := by rw [integral_mul_const, hI, one_mul]
  have hc₁ : Continuous (fun y => w y * u (x * y)) :=
    w.continuous.mul (u.continuous.comp (continuous_const.mul continuous_id))
  have hc₂ : Continuous (fun y => w y * u x) := w.continuous.mul continuous_const
  have hEq : (leftConvolution μ w u - u) x = ∫ y, w y * (u (x * y) - u x) ∂μ := by
    have hi : Integrable (fun y => w y * u (x * y)) μ :=
      hc₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hj : Integrable (fun y => w y * u x) μ :=
      hc₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [ContinuousMap.sub_apply, hright]
    nth_rw 1 [← hJ]
    rw [← integral_sub hi hj]
    exact integral_congr_ae (ae_of_all _ fun _ => (mul_sub _ _ _).symm)
  have hq (y : O n) : 0 ≤ q y := by
    have hpeak : 0 ≤ polynomialPeak B y := by
      unfold polynomialPeak
      have hbe := (div_le_iff₀ (by positivity : 0 < 2 * B)).2 (hBnd y |>.trans (by linarith) :
        distSq y 1 ≤ 1 * (2 * B))
      linarith
    exact pow_nonneg hpeak _
  have hPoint (y : O n) :
      ‖w y * (u (x * y) - u x)‖ ≤ (L * K * n) * (Real.sqrt (distSq y 1) * q y / Z) := by
    have hqy : 0 ≤ q y / Z := div_nonneg (hq y) hZ'.le
    rw [norm_mul, hw, Complex.norm_real, Real.norm_of_nonneg hqy]
    have hD : (↑(x * y) : M n) - (x : M n) = (x : M n) * ((y : M n) - 1) := by
      simp only [Submonoid.coe_mul, mul_sub, mul_one]
    calc
      _ ≤ (q y / Z) * (L * ‖(↑(x * y) : M n) - (x : M n)‖) :=
        mul_le_mul_of_nonneg_left (hLip x (x * y)) hqy
      _ ≤ (q y / Z) * (L * (K * ((n : ℝ) * Real.sqrt (distSq y 1)))) := by
        rw [hD]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          ((norm_mul_le _ _).trans (mul_le_mul (hK x (mem_univ _))
            (norm_sub_one_le_distSq_sqrt y) (norm_nonneg _) hK₀)) hL) hqy
      _ = _ := by ring
  have hcJ : Continuous (fun y : O n => (L * K * n) * (Real.sqrt (distSq y 1) * q y / Z)) :=
    continuous_const.mul ((continuous_distSq_one.sqrt.mul
      ((continuous_polynomialPeak B).pow _)).div_const _)
  rw [hEq]
  calc
    _ ≤ ∫ y, ‖w y * (u (x * y) - u x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (L * K * n) * (Real.sqrt (distSq y 1) * q y / Z) ∂μ := by
      have hc : Continuous (fun y => ‖w y * (u (x * y) - u x)‖) :=
        (w.continuous.mul ((u.continuous.comp (continuous_const.mul continuous_id)).sub
          continuous_const)).norm
      exact integral_mono (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hcJ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hPoint
    _ ≤ _ := by
      rw [integral_const_mul, integral_div]
      have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ L * K * (n : ℝ))
      exact hm.trans_eq (by ring)

end Langlands.Archimedean.OrthogonalFinitePolynomial
