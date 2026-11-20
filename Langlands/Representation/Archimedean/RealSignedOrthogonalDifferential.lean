import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Differential of the signed orthogonal part -/

noncomputable section

open Matrix Filter
open scoped Matrix.Norms.Operator ContDiff Topology

namespace Langlands.Archimedean.RealSignedOrthogonalDifferential

open GramFormula PrincipalSeriesExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

local notation "Mat" k:max => Matrix (Fin k) (Fin k) ℝ

private theorem orthogonal_mul_transpose {U : Mat n}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℝ) : U * Uᵀ = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.mem_unitaryGroup_iff.mp hU)

/-- The signed orthogonal part is smooth at every invertible matrix. -/
theorem contDiffAt_signedOrthogonal {X : Mat n} (hX : IsUnit X) :
    ContDiffAt ℝ ∞ signedOrthogonal X := by
  have hGram (l : ℕ) : 0 < gram l X := by
    simpa only [hX.unit_spec] using gram_pos hX.unit l
  have h (l : ℕ) : ContDiffAt ℝ ∞ (fun Y : Mat n => (Real.sqrt (gram l Y))⁻¹) X :=
    (((Real.contDiffAt_sqrt (hGram l).ne').comp X (contDiff_gram l).contDiffAt).inv
      (Real.sqrt_pos.2 (hGram l)).ne')
  show ContDiffAt ℝ ∞ (fun Y : Mat n => Matrix.of fun i j =>
    gramColumn i j Y * (Real.sqrt (gram i Y))⁻¹ *
      (Real.sqrt (gram ((i : ℕ) + 1) Y))⁻¹) X
  let ofMatrix : (Fin n → Fin n → ℝ) →L[ℝ] Mat n :=
    (Matrix.ofLinearEquiv ℝ).toLinearMap.toContinuousLinearMap
  apply ofMatrix.contDiff.contDiffAt.comp X
  exact contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j =>
    (((contDiff_gramColumn i j).contDiffAt.mul (h i)).mul (h ((i : ℕ) + 1)))

/-- Multiplication by the transpose of the signed orthogonal part leaves an
upper triangular matrix. -/
theorem mul_transpose_signedOrthogonal_upper {X : Mat n} (hX : IsUnit X) :
    (X * (signedOrthogonal X)ᵀ).IsUpperTriangular := by
  obtain ⟨b, U, hb, hbu, hU, rfl⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary X hX
  have hd (i : Fin n) : b i i ≠ 0 := by
    have hdet := ((isUnit_iff_isUnit_det b).mp hbu).ne_zero
    rw [det_of_isUpperTriangular hb] at hdet
    exact fun hi => hdet (Finset.prod_eq_zero (f := fun j => b j j) (Finset.mem_univ i) hi)
  rw [signedOrthogonal_mul hb hd (orthogonal_mul_transpose hU), transpose_mul,
    diagonal_transpose]
  rw [show (b * U) * (Uᵀ * diagonal (fun i => signReal (b i i))) =
    b * (U * Uᵀ) * diagonal (fun i => signReal (b i i)) by simp only [mul_assoc],
    orthogonal_mul_transpose hU, mul_one]
  exact hb.mul (blockTriangular_diagonal _)

private theorem signedOrthogonal_diagonal_pos (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    signedOrthogonal (diagonal d) = 1 := by
  have h := signedOrthogonal_mul (b := diagonal d) (κ := (1 : Mat n))
    (blockTriangular_diagonal d) (fun i => by simpa using (hd i).ne') (by simp)
  simpa [signReal, hd] using h

/-- At a positive diagonal matrix, the derivative of the signed orthogonal
part is skew-symmetric. Its strictly lower entry in row `i`, column `j` is
the corresponding entry of the direction divided by the diagonal in row `i`. -/
def RealSignedOrthogonalDifferentialStatement : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ), (∀ i, 0 < d i) →
    ContDiffAt ℝ ∞ signedOrthogonal (diagonal d) ∧
      ∀ H : Matrix (Fin n) (Fin n) ℝ,
        let W := fderiv ℝ signedOrthogonal (diagonal d) H
        Wᵀ = -W ∧ ∀ i j : Fin n, j < i → W i j = H i j / d i

theorem realSignedOrthogonalDifferential : RealSignedOrthogonalDifferentialStatement := by
  intro n d hd
  let D : Mat n := diagonal d
  change ContDiffAt ℝ ∞ signedOrthogonal D ∧ ∀ H : Mat n, _
  have hD : IsUnit D := by
    change IsUnit (diagonal d)
    rw [isUnit_iff_isUnit_det, det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => (hd i).ne').isUnit
  have hnear : ∀ᶠ X in 𝓝 D, IsUnit X := Units.isOpen.mem_nhds hD
  have hval : signedOrthogonal D = 1 := signedOrthogonal_diagonal_pos d hd
  have hsmooth := contDiffAt_signedOrthogonal hD
  let K' := fderiv ℝ signedOrthogonal D
  have hk : HasFDerivAt signedOrthogonal K' D :=
    (hsmooth.differentiableAt (by simp)).hasFDerivAt
  let t : Mat n →L[ℝ] Mat n :=
    (transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap.toContinuousLinearMap
  have ht : HasFDerivAt (fun X : Mat n => (signedOrthogonal X)ᵀ) (t.comp K') D :=
    t.hasFDerivAt.comp D hk
  refine ⟨hsmooth, fun H => ?_⟩
  change (K' H)ᵀ = -(K' H) ∧ ∀ i j : Fin n, j < i → (K' H) i j = H i j / d i
  have hskew : (K' H)ᵀ = -(K' H) := by
    have hmul := hk.mul' ht
    have hEq : (fun X : Mat n => signedOrthogonal X * (signedOrthogonal X)ᵀ) =ᶠ[𝓝 D] fun _ => 1 :=
      hnear.mono fun X hX => by
        have hu := signedOrthogonal_mem hX.unit
        rw [hX.unit_spec] at hu
        exact orthogonal_mul_transpose hu
    have hzero := (hmul.congr_of_eventuallyEq hEq.symm).unique (hasFDerivAt_const (1 : Mat n) D)
    have h := congrArg (fun L : Mat n →L[ℝ] Mat n => L H) hzero
    change signedOrthogonal D * (K' H)ᵀ + K' H * (signedOrthogonal D)ᵀ = 0 at h
    rw [hval, one_mul, transpose_one, mul_one] at h
    exact eq_neg_iff_add_eq_zero.mpr h
  refine ⟨hskew, fun i j hij => ?_⟩
  have hmul := (hasFDerivAt_id (𝕜 := ℝ) D).mul' ht
  have hEq : (fun X : Mat n => Langlands.Archimedean.RealJacquetFrobenius.entryCLM i j (X * (signedOrthogonal X)ᵀ)) =ᶠ[𝓝 D] fun _ => 0 :=
    hnear.mono fun X hX => mul_transpose_signedOrthogonal_upper hX hij
  have hentry := (Langlands.Archimedean.RealJacquetFrobenius.entryCLM i j).hasFDerivAt.comp D hmul
  have hzero := (hentry.congr_of_eventuallyEq hEq.symm).unique (hasFDerivAt_const (0 : ℝ) D)
  have h := congrArg (fun L : Mat n →L[ℝ] ℝ => L H) hzero
  change (diagonal d * (K' H)ᵀ + H * (signedOrthogonal D)ᵀ) i j = 0 at h
  rw [hval, transpose_one, mul_one, Matrix.add_apply, diagonal_mul, hskew, Matrix.neg_apply] at h
  exact (eq_div_iff (hd i).ne').2 (by linarith)

end Langlands.Archimedean.RealSignedOrthogonalDifferential
