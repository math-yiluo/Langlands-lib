import Langlands.Representation.Archimedean.RealOrthogonalUncertainty
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Supremum derivative bounds for finite trigonometric expansions -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealBlockFourierFinite

private theorem norm_expMode (j : ℤ) (t : ℝ) : ‖expMode j t‖ = 1 := by
  rw [expMode, ← Complex.ofReal_intCast, ← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem norm_coeff_le {f : ℝ → ℂ} {A : ℝ} (hf : ∀ t, ‖f t‖ ≤ A) (j : ℤ) :
    ‖coeff j f‖ ≤ (2 * Real.pi) * A := by
  unfold coeff
  have h (t : ℝ) : ‖f t * Complex.exp (-((j : ℂ) * (t : ℂ) * Complex.I))‖ ≤ A := by
    have he : Complex.exp (-((j : ℂ) * (t : ℂ) * Complex.I)) = expMode (-j) t := by
      rw [expMode, Int.cast_neg]
      congr 1
      ring
    simpa only [he, norm_mul, norm_expMode, mul_one] using hf t
  have hM := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (fun t _ => h t)
  rw [sub_zero, abs_of_pos (mul_pos two_pos Real.pi_pos), mul_comm A] at hM
  exact hM

/-- A trigonometric polynomial of degree at most `N` and uniform norm at most `A`
has derivative bounded by `(2N+1) N A`. -/
def TrigonometricDerivativeBoundStatement : Prop :=
  ∀ (N : ℕ) (f : ℝ → ℂ) (A : ℝ), 0 ≤ A →
    f ∈ trigPoly N → (∀ t, ‖f t‖ ≤ A) →
    ∀ t : ℝ, ∃ z : ℂ, HasDerivAt f z t ∧
      ‖z‖ ≤ (2 * (N : ℝ) + 1) * (N : ℝ) * A

/-- Fourier inversion writes the derivative as a finite sum in which each normalized
coefficient has norm at most `A` and each occurring frequency has magnitude at most `N`. -/
theorem trigonometricDerivativeBound : TrigonometricDerivativeBoundStatement := by
  intro N f A hA hf hNorm t
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let c := (2 * (Real.pi : ℂ))⁻¹
  let D (j : ℤ) := coeff j f * (Complex.I * j * expMode j t)
  refine ⟨c * ∑ j ∈ S, D j, ?_, ?_⟩
  · have he : f = fun s => c * ∑ j ∈ S, coeff j f * expMode j s :=
      funext (eq_sum_coeff_of_mem_trigPoly hf)
    have hd := HasDerivAt.fun_sum (u := S) (A := fun j s => coeff j f * expMode j s)
      (A' := D) (x := t) (fun j _ => (RealOrthogonalUncertainty.hasDerivAt_expMode j t).const_mul _)
    rw [he]
    exact hd.const_mul c
  · have hD (j : ℤ) (hj : j ∈ S) : ‖D j‖ ≤ (2 * Real.pi) * A * (N : ℝ) := by
      have hj' : |j| ≤ (N : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hj)
      have hjR : |(j : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hj'
      simp only [D, norm_mul, Complex.norm_I, one_mul, norm_expMode, mul_one,
        Complex.norm_intCast]
      exact mul_le_mul (norm_coeff_le hNorm j) hjR (abs_nonneg _) (by positivity)
    have hπ : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
    have hc : ‖c‖ = (2 * Real.pi)⁻¹ := by
      rw [show c = (2 * (Real.pi : ℂ))⁻¹ from rfl, norm_inv, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
    have hS : S.card = 2 * N + 1 := by
      rw [show S = Finset.Icc (-(N : ℤ)) (N : ℤ) from rfl, Int.card_Icc]
      omega
    calc
      ‖c * ∑ j ∈ S, D j‖ = (2 * Real.pi)⁻¹ * ‖∑ j ∈ S, D j‖ := by rw [norm_mul, hc]
      _ ≤ (2 * Real.pi)⁻¹ * ∑ j ∈ S, ‖D j‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hπ.le)
      _ ≤ (2 * Real.pi)⁻¹ * ∑ j ∈ S, (2 * Real.pi) * A * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hD) (inv_nonneg.mpr hπ.le)
      _ = _ := by
        simp only [Finset.sum_const, hS, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_one]
        field_simp

/-- Along a curve of orthogonal matrices with trigonometric entries of degree at most one,
the restriction of an entry polynomial of degree at most `N` has trigonometric degree
at most `N`. -/
theorem comp_mem_trigPoly_of_mem_degreeLE {n N : ℕ}
    {f : Matrix.unitaryGroup (Fin n) ℝ → ℂ} (hf : f ∈ RealKTypeCount.degreeLE n N)
    (γ : ℝ → Matrix.unitaryGroup (Fin n) ℝ)
    (hγ : ∀ ij : Fin n × Fin n, (fun t => OrthogonalFinitePolynomial.entry n ij (γ t)) ∈ trigPoly 1) :
    (fun t => f (γ t)) ∈ trigPoly N := by
  let A : (Matrix.unitaryGroup (Fin n) ℝ → ℂ) →ₐ[ℂ] (ℝ → ℂ) :=
    AlgHom.pi fun t => Pi.evalAlgHom ℂ (fun _ : Matrix.unitaryGroup (Fin n) ℝ => ℂ) (γ t)
  have hlinear : (RealKTypeCount.linearSpan n).map A.toLinearMap ≤ trigPoly 1 := by
    rw [RealKTypeCount.linearSpan, Submodule.map_sup, Submodule.map_one, Submodule.map_span]
    refine sup_le (Submodule.one_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · exact trigPoly_mono zero_le_one (const_mem_trigPoly 1)
    · rintro _ ⟨_, ⟨ij, rfl⟩, rfl⟩
      exact hγ ij
  have hmap : (RealKTypeCount.degreeLE n N).map A.toLinearMap ≤ trigPoly N := by
    rw [RealKTypeCount.degreeLE, Submodule.map_pow]
    exact (pow_le_pow_left' hlinear N).trans (Langlands.Archimedean.RealOrthogonalUncertainty.trigPoly_one_pow_le N)
  exact hmap ⟨f, hf, rfl⟩

open RealBlockRotation in
/-- Right rotation by a standard two-plane has the expected trigonometric degree bound. -/
theorem right_blockRotation_mem_trigPoly {n N p : ℕ} (hp : p + 1 < n)
    {f : Matrix.unitaryGroup (Fin n) ℝ → ℂ} (hf : f ∈ RealKTypeCount.degreeLE n N)
    (x : Matrix.unitaryGroup (Fin n) ℝ) :
    (fun t => f (x * ⟨(blockRotation n p t : Matrix (Fin n) (Fin n) ℝ),
      blockRotation_mem_unitaryCompact n p t⟩)) ∈ trigPoly N := by
  apply comp_mem_trigPoly_of_mem_degreeLE hf
  intro ij
  let A := (x : Matrix (Fin n) (Fin n) ℝ)
  have h (t : ℝ) : (A * (blockRotation n p t : Matrix (Fin n) (Fin n) ℝ)) ij.1 ij.2 =
      A ij.1 ij.2 + (Real.cos t - 1) * (A * blockProj hp) ij.1 ij.2 +
        Real.sin t * (A * rotationGenerator n p) ij.1 ij.2 := by
    rw [blockRotation_val_eq hp]
    simp only [rotMatrix, Matrix.mul_add, Matrix.mul_smul, mul_one, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
  change (fun t => (((A * (blockRotation n p t : Matrix (Fin n) (Fin n) ℝ))
    ij.1 ij.2 : ℝ) : ℂ)) ∈ trigPoly 1
  simp_rw [h]
  push_cast
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    (affine_mem_trigPoly (A ij.1 ij.2) ((A * blockProj hp) ij.1 ij.2)
      ((A * rotationGenerator n p) ij.1 ij.2))

end Langlands.Archimedean.RealBlockFourierFinite
