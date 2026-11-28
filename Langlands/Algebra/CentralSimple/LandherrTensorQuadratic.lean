import Langlands.Algebra.CentralSimple.LandherrNormSemilinear

/-! # Coordinates on `E ⊗_F R` and multiplicative Hilbert 90 -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.SU3Root
open scoped TensorProduct

universe u

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (R : Type u) [CommRing R] [Algebra F R]

/-- The element `1 ⊗ p + r ⊗ q` of `E ⊗_F R`. -/
def qm (p q : R) : E ⊗[F] R := (1 : E) ⊗ₜ p + skewRoot F E ⊗ₜ q

/-- The coordinate functionals of `E` over `F` for the basis `1, r`. -/
def skewCoord (i : Fin 2) : E →ₗ[F] F :=
  ((QuadraticAlgebra.basis (skewSq F E) 0).coord i).comp
    (quadraticEquiv F E).symm.toLinearEquiv.toLinearMap

theorem skewCoord_one (i : Fin 2) : skewCoord F E i 1 = if i = 0 then 1 else 0 := by
  have : (quadraticEquiv F E).symm 1 = 1 := map_one _
  fin_cases i <;> simp [skewCoord, this, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem skewCoord_skewRoot (i : Fin 2) :
    skewCoord F E i (skewRoot F E) = if i = 0 then 0 else 1 := by
  have : (quadraticEquiv F E).symm (skewRoot F E) = QuadraticAlgebra.omega :=
    (AlgEquiv.symm_apply_eq _).mpr (quadraticEquiv_omega F E).symm
  fin_cases i <;> simp [skewCoord, this]

/-- The coordinate maps `E ⊗_F R → R`. -/
def tensorCoord (i : Fin 2) : E ⊗[F] R →ₗ[F] R :=
  (TensorProduct.lid F R).toLinearMap ∘ₗ (skewCoord F E i).rTensor R

theorem tensorCoord_qm (p q : R) :
    tensorCoord F E R 0 (qm F E R p q) = p ∧ tensorCoord F E R 1 (qm F E R p q) = q := by
  simp [tensorCoord, qm, skewCoord_one, skewCoord_skewRoot]

theorem qm_injective {p q p' q' : R} (h : qm F E R p q = qm F E R p' q') : p = p' ∧ q = q' := by
  have h0 := congrArg (tensorCoord F E R 0) h
  have h1 := congrArg (tensorCoord F E R 1) h
  rw [(tensorCoord_qm F E R p q).1, (tensorCoord_qm F E R p' q').1] at h0
  rw [(tensorCoord_qm F E R p q).2, (tensorCoord_qm F E R p' q').2] at h1
  exact ⟨h0, h1⟩

theorem exists_eq_qm (z : E ⊗[F] R) : ∃ p q : R, z = qm F E R p q :=
  exists_eq_one_tmul_add_skewRoot_tmul' F E R z

theorem qm_add (p q p' q' : R) :
    qm F E R p q + qm F E R p' q' = qm F E R (p + p') (q + q') := by
  simp only [qm, TensorProduct.tmul_add]
  abel

theorem skewRoot_mul_tmul (x : R) :
    (skewRoot F E * skewRoot F E) ⊗ₜ[F] x = (1 : E) ⊗ₜ (algebraMap F R (skewSq F E) * x) := by
  rw [← algebraMap_skewSq, Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul,
    Algebra.smul_def]

theorem qm_mul (p q p' q' : R) :
    qm F E R p q * qm F E R p' q' =
      qm F E R (p * p' + algebraMap F R (skewSq F E) * (q * q')) (p * q' + q * p') := by
  simp only [qm, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [skewRoot_mul_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add]
  abel

theorem tensorConj_qm (p q : R) : tensorConj F E R (qm F E R p q) = qm F E R p (-q) := by
  simp [qm, conjugation_skewRoot, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

theorem qm_one : qm F E R 1 0 = 1 := by
  simp [qm, Algebra.TensorProduct.one_def]

theorem one_tmul_eq_qm (p : R) : (1 : E) ⊗ₜ[F] p = qm F E R p 0 := by simp [qm]

/-- The quadratic norm `z σ(z)` in coordinates. -/
theorem qm_mul_tensorConj (p q : R) :
    qm F E R p q * tensorConj F E R (qm F E R p q) =
      qm F E R (p * p - algebraMap F R (skewSq F E) * (q * q)) 0 := by
  rw [tensorConj_qm, qm_mul]
  congr 1 <;> ring

variable {R} in
/-- Over a field, `z` is a unit as soon as its quadratic norm is nonzero. -/
theorem isUnit_qm_of_norm_ne_zero {K : Type u} [Field K] [Algebra F K] (p q : K)
    (h : p * p - algebraMap F K (skewSq F E) * (q * q) ≠ 0) : IsUnit (qm F E K p q) := by
  set N := p * p - algebraMap F K (skewSq F E) * (q * q)
  refine isUnit_iff_exists_inv.mpr ⟨qm F E K (p * N⁻¹) (-q * N⁻¹), ?_⟩
  rw [qm_mul, ← qm_one]
  congr 1
  · field_simp
    ring
  · ring

/-- **Multiplicative Hilbert 90 in `E ⊗_F K`.** If `c σ(c) = 1` then `c = ω / σ(ω)` for an
invertible `ω`, written as `ω = c σ(ω)`. -/
theorem exists_hilbert90 (K : Type u) [Field K] [Algebra F K] (c : E ⊗[F] K)
    (hc : c * tensorConj F E K c = 1) :
    ∃ P Q : K, IsUnit (qm F E K P Q) ∧ qm F E K P Q = c * tensorConj F E K (qm F E K P Q) := by
  have hK : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  obtain ⟨p, q, rfl⟩ := exists_eq_qm F E K c
  set d := algebraMap F K (skewSq F E)
  have hn : p * p - d * (q * q) = 1 := by
    rw [qm_mul_tensorConj, ← qm_one] at hc
    exact (qm_injective F E K hc).1
  have hd : d ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F K).injective]
    intro h0
    have := algebraMap_skewSq F E
    rw [h0, map_zero] at this
    exact skewRoot_ne_zero F E (mul_self_eq_zero.mp this.symm)
  by_cases h1 : p + 1 = 0
  · refine ⟨-d * q, 1 - p, isUnit_qm_of_norm_ne_zero F E _ _ ?_, ?_⟩
    · have hp : p = -1 := by linear_combination h1
      intro h0
      apply hd
      have : (-d * q) * (-d * q) - d * ((1 - p) * (1 - p)) = d * (2 * (p - 1)) := by
        linear_combination (-d) * hn
      rw [this, hp] at h0
      have h4 : (4 : K) ≠ 0 := by norm_num
      have : d * 4 = 0 := by linear_combination -h0
      exact (mul_eq_zero.mp this).resolve_right h4
    · rw [tensorConj_qm, qm_mul]
      congr 1
      · ring
      · linear_combination -hn
  · refine ⟨1 + p, q, isUnit_qm_of_norm_ne_zero F E _ _ ?_, ?_⟩
    · have : (1 + p) * (1 + p) - d * (q * q) = 2 * (p + 1) := by linear_combination hn
      rw [this]
      exact mul_ne_zero two_ne_zero h1
    · rw [tensorConj_qm, qm_mul]
      congr 1
      · linear_combination -hn
      · ring

end Langlands.CentralSimple.Landherr
