import Langlands.LinearAlgebra.SiegelUpperHalfSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Gaussian integrals over the Siegel upper half space

For `σ` in the Siegel upper half space, `siegelGaussianIntegral σ = ∫ e^{πi xᵀ σ x} dx` over `ℝ^ι`
satisfies `siegelGaussianIntegral σ ^ 2 · det (-iσ) = 1`

(`Matrix.IsSiegel.siegelGaussianIntegral_sq_mul_det`), more generally
`∫ e^{πi xᵀ σ x + 2πi wᵀ x} dx = siegelGaussianIntegral σ · e^{-πi wᵀ σ⁻¹ w}`
(`Matrix.IsSiegel.integral_cexp_quadratic`). The proof diagonalizes `σ = Pᵀ (diagonal t) P` over `ℝ`
(`Matrix.IsSiegel.exists_eq_transpose_mul_diagonal_mul`), changes variables by `P` and reduces to the
one-dimensional Gaussian integrals of Mathlib. Consequence: the pairing of a Siegel Gaussian with the
standard Gaussian, `(∫ c e^{πi xᵀ τ x} · e^{-π xᵀ x} dx)² · det (1 - iτ) = c²`
(`siegelGaussian_pair_standardGaussian`).
-/

open Complex Matrix MeasureTheory
open scoped Real ComplexConjugate

noncomputable section

namespace Langlands

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∫ e^{πi xᵀ σ x} dx` over `ℝ^ι` (a Bochner integral). -/
def siegelGaussianIntegral {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) : ℂ :=
  ∫ x : ι → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))))

/-- Linear change of variables by an invertible real matrix in an integral over `ℝ^ι`. -/
theorem integral_comp_mulVec_of_det_ne_zero {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    ∫ x, f (P *ᵥ x) = (|P.det⁻¹| : ℝ) * ∫ y, f y := by
  have h := integral_map (μ := (volume : Measure (ι → ℝ))) (φ := toLin' P) (f := f)
    (toLin' P).continuous_of_finiteDimensional.measurable.aemeasurable hf.aestronglyMeasurable
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hP, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), real_smul] at h
  rw [h]
  rfl

/-- For `σ` Siegel, `∫ e^{πi xᵀ σ x + 2πi wᵀ x} dx = s · e^{-πi wᵀ σ⁻¹ w}` for a constant `s` with
`s² · det (-iσ) = 1`. -/
theorem Matrix.IsSiegel.exists_integral_cexp_quadratic {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) :
    ∃ s : ℂ, s ^ 2 * (-I • σ).det = 1 ∧ ∀ w : ι → ℂ,
      ∫ x : ι → ℝ, cexp (2 * π * I * (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 +
        (fun i => (x i : ℂ)) ⬝ᵥ w)) = s * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  have ht0 (i : ι) : t i ≠ 0 := fun h0 => by simpa [h0] using ht i
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu := Matrix.isUnit_det_map_ofReal hP
  refine ⟨(|P.det⁻¹| : ℝ) * ∏ i, (π / (-(π * I * t i))) ^ (1 / 2 : ℂ), ?_, fun w => ?_⟩
  · have e : (P.map ofReal).det = (P.det : ℂ) := (ofRealHom.map_det P).symm
    have e2 (i : ι) : ((π / (-(π * I * t i))) ^ (1 / 2 : ℂ)) ^ 2 * (-I * t i) = 1 := by
      rw [one_div, cpow_ofNat_inv_pow]
      field_simp [ht0 i]
    have e3 : (P.det : ℂ) ≠ 0 := by exact_mod_cast hP
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul, det_mul, det_mul, det_transpose,
      det_diagonal, e, mul_pow, ← ofReal_pow, sq_abs, ← Finset.prod_pow]
    have e4 := Finset.prod_congr (s₁ := Finset.univ) rfl fun i _ => e2 i
    rw [Finset.prod_mul_distrib, Finset.prod_const_one] at e4
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    have e5 : (P.det : ℂ)⁻¹ ^ 2 * P.det * P.det = 1 := by field_simp
    linear_combination ((P.det : ℂ)⁻¹ ^ 2 * P.det * P.det) * e4 + e5
  set v := ((P.map ofReal)ᵀ)⁻¹ *ᵥ w with hv
  have hw : w = (P.map ofReal)ᵀ *ᵥ v := by
    rw [hv, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_transpose _ hu), one_mulVec]
  have hb (i : ι) : 0 < (-(π * I * t i)).re := by simpa using mul_pos Real.pi_pos (ht i)
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add hb fun i => 2 * π * I * v i
  have hc := integral_comp_mulVec_of_det_ne_zero hP (f := fun y : ι → ℝ =>
    cexp (-∑ i, -(π * I * t i) * (y i : ℂ) ^ 2 + ∑ i, 2 * π * I * v i * y i)) (by fun_prop)
  rw [key, Finset.prod_mul_distrib, ← Complex.exp_sum, ← mul_assoc] at hc
  convert hc using 3 with x
  · congr 1
    have e := Matrix.ofReal_mulVec_eq P x
    rw [hw, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec _ _ v,
      vecMul_transpose, ← e]
    simp only [dotProduct, mulVec_diagonal, Finset.sum_div, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_diagonal_of_ne_zero ht0, ← mulVec_mulVec,
      ← mulVec_mulVec, ← hv, dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, ← hv]
    simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [ht0 i]
    ring

/-- `∫ e^{πi xᵀ σ x + 2πi wᵀ x} dx = siegelGaussianIntegral σ · e^{-πi wᵀ σ⁻¹ w}`. -/
theorem Matrix.IsSiegel.integral_cexp_quadratic {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) (w : ι → ℂ) :
    ∫ x : ι → ℝ, cexp (2 * π * I * (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 +
        (fun i => (x i : ℂ)) ⬝ᵥ w)) =
      siegelGaussianIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) := by
  obtain ⟨s, -, hs⟩ := h.exists_integral_cexp_quadratic
  have h0 := hs 0
  simp only [dotProduct_zero, zero_dotProduct, add_zero, mul_zero, Complex.exp_zero,
    mul_one] at h0
  rw [hs, ← h0, siegelGaussianIntegral]
  congr 2 with x
  ring_nf

/-- `siegelGaussianIntegral σ ² · det (-iσ) = 1`. -/
theorem Matrix.IsSiegel.siegelGaussianIntegral_sq_mul_det {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) :
    siegelGaussianIntegral σ ^ 2 * (-I • σ).det = 1 := by
  obtain ⟨s, hs1, hs⟩ := h.exists_integral_cexp_quadratic
  have h0 := (h.integral_cexp_quadratic 0).symm.trans (hs 0)
  rw [mul_left_inj' (Complex.exp_ne_zero _)] at h0
  rwa [h0]

/-- The Gaussian integral of a Siegel matrix does not vanish. -/
theorem Matrix.IsSiegel.siegelGaussianIntegral_ne_zero {σ : Matrix ι ι ℂ} (h : Matrix.IsSiegel σ) :
    siegelGaussianIntegral σ ≠ 0 := fun h0 => by
  simpa [h0] using h.siegelGaussianIntegral_sq_mul_det

/-- The pairing of `c e^{πi xᵀ τ x}` with the standard Gaussian: its square times
`det (1 - iτ)` is `c²`. -/
theorem siegelGaussian_pair_standardGaussian (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ) (hτ : Matrix.IsSiegel τ) :
    (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  set σ : Matrix l l ℂ := τ + I • (1 : Matrix l l ℂ) with hσdef
  have hσ : Matrix.IsSiegel σ := by
    refine ⟨?_, ?_⟩
    · exact hτ.1.add (by simp [Matrix.IsSymm, Matrix.transpose_smul])
    · have : σ.map Complex.im = τ.map Complex.im + 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [σ]
        · simp [σ, hij]
      rw [this]
      exact hτ.2.add_posSemidef Matrix.PosSemidef.one
  have hint : ∀ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))
      = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ)))) := by
    intro x
    rw [← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
    congr 2
    have e : ((x ⬝ᵥ x : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      simp [dotProduct]
    rw [e, hσdef, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [map_mul, map_neg, conj_ofReal, smul_eq_mul]
    have : conj ((fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      simp [dotProduct, map_sum]
    rw [this]
    ring_nf
    simp [I_sq]
    ring
  have hdet : (1 - I • τ) = -I • σ := by
    rw [hσdef, smul_add, smul_smul]
    simp [neg_smul, sub_eq_add_neg, add_comm]
  simp_rw [hint]
  rw [integral_const_mul, hdet, mul_pow, mul_assoc]
  have := hσ.siegelGaussianIntegral_sq_mul_det
  rw [siegelGaussianIntegral] at this
  rw [this, mul_one]

end Langlands
