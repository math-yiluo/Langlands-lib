import Langlands.Representation.Archimedean.RealBlockRotation
import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Left derivatives and the block Fourier coefficients

For a smooth function `φ` on `GL_N(ℝ)` with `φ(exp(diag x) u g) = exp(∑ αᵢ xᵢ) φ(g)` (for
example an element of a principal series) and an upper triangular matrix `A`, the `j`-th block
Fourier coefficient in the coordinates `p, q = p + 1` of the derivative of `φ` in the direction
`r_p(θ) A g` is a combination of the coefficients of index `j - 2`, `j`, `j + 2` of `φ` at `g`
(`integral_fderiv_blockRotation_mul_mul`). This gives the same formula for the block Fourier
coefficients of a right derivative `R_X φ` when `g X = A g`
(`blockFourierCoefficient_rightDerivative`), and for the derivative of `s ↦ Φ_j(φ)(γ s)` along a
`C¹` path with `γ' = A γ` (`hasDerivAt_blockFourierCoefficient_comp`).

The proof writes `r A r⁻¹ = U + κ W` with `U` upper triangular and `W` the rotation generator,
evaluates the `U`-part by the equivariance and integrates the `W`-part by parts in `θ`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace RealBlockDerivative

open RealBlockRotation RealPrincipalSeriesDuality

variable {N p : ℕ}

/-! ## Products with block rotations -/

theorem blockRotation_mul_apply (h : p + 1 < N) (θ : ℝ) (M : Matrix (Fin N) (Fin N) ℝ)
    (i k : Fin N) :
    ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * M) i k =
      if (i : ℕ) = p then Real.cos θ * M (ia h) k - Real.sin θ * M (ib h) k
      else if (i : ℕ) = p + 1 then Real.sin θ * M (ia h) k + Real.cos θ * M (ib h) k
      else M i k := by
  rw [Matrix.mul_apply]
  have hne := ia_ne_ib h
  split_ifs with h1 h2
  · rw [Finset.sum_eq_add_of_mem (ia h) (ib h) (Finset.mem_univ _) (Finset.mem_univ _) hne]
    · rw [blockRotation_apply h, blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · intro c _ hc
      rw [blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, ne_eq, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
  · rw [Finset.sum_eq_add_of_mem (ia h) (ib h) (Finset.mem_univ _) (Finset.mem_univ _) hne]
    · rw [blockRotation_apply h, blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · intro c _ hc
      rw [blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, ne_eq, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
  · rw [Finset.sum_eq_single i]
    · rw [blockRotation_apply h]
      simp only [Fin.ext_iff, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · intro c _ hc
      rw [blockRotation_apply h]
      simp only [Fin.ext_iff, ne_eq, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · simp

theorem mul_blockRotation_apply (h : p + 1 < N) (θ : ℝ) (M : Matrix (Fin N) (Fin N) ℝ)
    (i k : Fin N) :
    (M * (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ)) i k =
      if (k : ℕ) = p then Real.cos θ * M i (ia h) + Real.sin θ * M i (ib h)
      else if (k : ℕ) = p + 1 then -Real.sin θ * M i (ia h) + Real.cos θ * M i (ib h)
      else M i k := by
  rw [Matrix.mul_apply]
  have hne := ia_ne_ib h
  split_ifs with h1 h2
  · rw [Finset.sum_eq_add_of_mem (ia h) (ib h) (Finset.mem_univ _) (Finset.mem_univ _) hne]
    · rw [blockRotation_apply h, blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · intro c _ hc
      rw [blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, ne_eq, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
  · rw [Finset.sum_eq_add_of_mem (ia h) (ib h) (Finset.mem_univ _) (Finset.mem_univ _) hne]
    · rw [blockRotation_apply h, blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · intro c _ hc
      rw [blockRotation_apply h]
      simp only [ia, ib, Fin.ext_iff, ne_eq, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
  · rw [Finset.sum_eq_single k]
    · rw [blockRotation_apply h]
      simp only [Fin.ext_iff, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · intro c _ hc
      rw [blockRotation_apply h]
      simp only [Fin.ext_iff, ne_eq, and_true, true_and, true_or, or_true] at *
      split_ifs <;> first | (exfalso; omega) | ring1
    · simp

/-! ## Conjugating an upper triangular matrix by a block rotation -/

/-- The conjugate `r_p(θ) A r_p(-θ)`. -/
def conj (N p : ℕ) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A *
    (blockRotation N p (-θ) : Matrix (Fin N) (Fin N) ℝ)

/-- The entry `κ = cos θ sin θ (A_pp - A_qq) - sin² θ A_pq` below the diagonal. -/
def kappa (h : p + 1 < N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  Real.cos θ * Real.sin θ * (A (ia h) (ia h) - A (ib h) (ib h)) -
    Real.sin θ ^ 2 * A (ia h) (ib h)

theorem conj_apply (h : p + 1 < N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (i k : Fin N) :
    conj N p θ A i k =
      if (k : ℕ) = p then
        Real.cos θ * ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A) i (ia h) -
          Real.sin θ * ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A) i (ib h)
      else if (k : ℕ) = p + 1 then
        Real.sin θ * ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A) i (ia h) +
          Real.cos θ * ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A) i (ib h)
      else ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A) i k := by
  rw [conj, mul_blockRotation_apply h, Real.cos_neg, Real.sin_neg]
  split_ifs <;> ring

theorem conj_lower (h : p + 1 < N) (θ : ℝ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsUpperTriangular) {i k : Fin N} (hik : k < i) :
    conj N p θ A i k = if (i : ℕ) = p + 1 ∧ (k : ℕ) = p then kappa h θ A else 0 := by
  have z : ∀ i' k' : Fin N, (k' : ℕ) < i' → A i' k' = 0 := fun i' k' hlt => hA hlt
  have hik' : (k : ℕ) < i := hik
  rw [conj_apply h, blockRotation_mul_apply h, blockRotation_mul_apply h,
    blockRotation_mul_apply h, kappa]
  have hne := ia_ne_ib h
  simp only [ia, ib] at *
  split_ifs <;>
    simp (disch := first | omega | (simp only [Fin.val_mk]; omega)) only [z, mul_zero,
      sub_zero, zero_add, add_zero, zero_sub, neg_zero]
  ring_nf

theorem conj_diag (h : p + 1 < N) (θ : ℝ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsUpperTriangular) (i : Fin N) :
    conj N p θ A i i =
      if (i : ℕ) = p then
        Real.cos θ ^ 2 * A (ia h) (ia h) - Real.cos θ * Real.sin θ * A (ia h) (ib h) +
          Real.sin θ ^ 2 * A (ib h) (ib h)
      else if (i : ℕ) = p + 1 then
        Real.sin θ ^ 2 * A (ia h) (ia h) + Real.cos θ * Real.sin θ * A (ia h) (ib h) +
          Real.cos θ ^ 2 * A (ib h) (ib h)
      else A i i := by
  have z : ∀ i' k' : Fin N, (k' : ℕ) < i' → A i' k' = 0 := fun i' k' hlt => hA hlt
  rw [conj_apply h, blockRotation_mul_apply h, blockRotation_mul_apply h,
    blockRotation_mul_apply h]
  have hne := ia_ne_ib h
  simp only [ia, ib] at *
  split_ifs <;>
    simp (disch := first | omega | (simp only [Fin.val_mk]; omega)) only [z, mul_zero,
      sub_zero, zero_add, add_zero, zero_sub, neg_zero] <;>
    ring_nf

/-! ## The decomposition `r A r⁻¹ = U + κ W` -/

/-- The upper triangular part `U = r A r⁻¹ - κ W` of the conjugate. -/
def upperPart (h : p + 1 < N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  conj N p θ A - kappa h θ A • rotationGenerator N p

theorem upperPart_isUpperTriangular (h : p + 1 < N) (θ : ℝ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsUpperTriangular) : (upperPart h θ A).IsUpperTriangular := by
  intro i k hik
  have hlt : k < i := hik
  have hik' : (k : ℕ) < i := hik
  simp only [upperPart, Matrix.sub_apply, Matrix.smul_apply, rotationGenerator_apply,
    smul_eq_mul]
  rw [conj_lower h θ hA hlt]
  split_ifs <;> first | (exfalso; omega) | ring

theorem upperPart_diag (h : p + 1 < N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    upperPart h θ A i i = conj N p θ A i i := by
  simp only [upperPart, Matrix.sub_apply, Matrix.smul_apply, rotationGenerator_apply,
    smul_eq_mul]
  split_ifs <;> first | (exfalso; omega) | ring

/-- `r A g = (U + κ W) (r g)`. -/
theorem blockRotation_mul_mul (h : p + 1 < N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (g : Langlands.GeneralLinear N ℝ) :
    (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A * (g : Matrix (Fin N) (Fin N) ℝ) =
      (upperPart h θ A + kappa h θ A • rotationGenerator N p) *
        ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) := by
  rw [upperPart, sub_add_cancel, conj, Units.val_mul, blockRotation_neg]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

/-- `∑ α_i U_ii = ∑ α_i A_ii - (α_p - α_{p+1}) (sin² θ (A_pp - A_qq) + cos θ sin θ A_pq)`. -/
theorem sum_upperPart_diag (h : p + 1 < N) (θ : ℝ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsUpperTriangular) (α : Fin N → ℂ) :
    ∑ i, α i * (upperPart h θ A i i : ℂ) =
      ∑ i, α i * (A i i : ℂ) - (α (ia h) - α (ib h)) *
        ((Real.sin θ ^ 2 * (A (ia h) (ia h) - A (ib h) (ib h)) +
          Real.cos θ * Real.sin θ * A (ia h) (ib h) : ℝ) : ℂ) := by
  have key : ∀ i, α i * (upperPart h θ A i i : ℂ) =
      α i * (A i i : ℂ) +
        (if i = ia h then α (ia h) * ((Real.cos θ ^ 2 * A (ia h) (ia h) -
          Real.cos θ * Real.sin θ * A (ia h) (ib h) + Real.sin θ ^ 2 * A (ib h) (ib h) -
            A (ia h) (ia h) : ℝ) : ℂ) else 0) +
        (if i = ib h then α (ib h) * ((Real.sin θ ^ 2 * A (ia h) (ia h) +
          Real.cos θ * Real.sin θ * A (ia h) (ib h) + Real.cos θ ^ 2 * A (ib h) (ib h) -
            A (ib h) (ib h) : ℝ) : ℂ) else 0) := by
    intro i
    rw [upperPart_diag, conj_diag h θ hA]
    by_cases ha : i = ia h
    · have hb : i ≠ ib h := ha ▸ ia_ne_ib h
      have hv : (i : ℕ) = p := by rw [ha]; rfl
      rw [ite_eq_left hv, ite_eq_left ha, ite_eq_right hb, ha]
      push_cast
      ring
    · by_cases hb : i = ib h
      · have hv : (i : ℕ) = p + 1 := by rw [hb]; rfl
        have hv' : ¬ (i : ℕ) = p := by omega
        rw [ite_eq_right hv', ite_eq_left hv, ite_eq_right ha, ite_eq_left hb, hb]
        push_cast
        ring
      · have hv : ¬ (i : ℕ) = p := fun e => ha (Fin.ext e)
        have hv' : ¬ (i : ℕ) = p + 1 := fun e => hb (Fin.ext e)
        rw [ite_eq_right hv, ite_eq_right hv', ite_eq_right ha, ite_eq_right hb]
        ring
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  push_cast
  linear_combination (α (ia h) * (A (ia h) (ia h) : ℂ) + α (ib h) * (A (ib h) (ib h) : ℂ)) *
    Complex.sin_sq_add_cos_sq (θ : ℂ)

/-! ## Functions with an exponential left equivariance -/

/-- `φ(exp(diag x) u g) = exp(∑ᵢ αᵢ xᵢ) φ(g)` for real `x` and upper unipotent `u`. -/
def IsExpEquivariant (α : Fin N → ℂ) (φ : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  ∀ (x : Fin N → ℝ) (u : Langlands.GeneralLinear.upperUnipotent N ℝ)
    (g : Langlands.GeneralLinear N ℝ),
    φ (matrixExpUnit N (Matrix.diagonal x) * (u : Langlands.GeneralLinear N ℝ) * g) =
      Complex.exp (∑ i, α i * (x i : ℂ)) * φ g

/-- Elements of a principal series of characters `χ_i(e^x) = e^{τ_i x}` satisfy
`IsExpEquivariant` with the `ρ`-shifted exponents `αᵢ = τᵢ + (N - 1)/2 - i`. -/
theorem isExpEquivariant_of_mem_principalSeries {χ : ℕ → ℝˣ → ℂ} {τ : Fin N → ℂ}
    (hχ : ∀ (i : Fin N) (x : ℝ),
      χ i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = Complex.exp (τ i * x))
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ principalSeries ℝ N χ) :
    IsExpEquivariant (fun i => τ i + ((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) f := by
  intro x u g
  rw [matrixExpUnit_diagonal, ((mem_principalSeries_iff ℝ N χ f).mp hf).2 _ u g]
  congr 1
  unfold principalSeriesCharacter
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hn : ‖((Units.mk0 (Real.exp (x i)) (Real.exp_pos (x i)).ne' : ℝˣ) : ℝ)‖ ^
      Module.finrank ℝ ℝ = Real.exp (x i) := by
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hn, ofReal_exp_cpow, hχ, ← Complex.exp_add]
  congr 1
  ring

/-- The derivative of an exp-equivariant function in an upper triangular direction:
`dφ_k(U k) = (∑ᵢ αᵢ Uᵢᵢ) φ(k)`. -/
theorem fderiv_upperTriangular_of_isExpEquivariant {α : Fin N → ℂ}
    {φ : Langlands.GeneralLinear N ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) (hα : IsExpEquivariant α φ)
    (k : Langlands.GeneralLinear N ℝ) {U : Matrix (Fin N) (Fin N) ℝ}
    (hU : U.IsUpperTriangular) :
    fderiv ℝ (unitsExtension φ) (k : Matrix (Fin N) (Fin N) ℝ)
        (U * (k : Matrix (Fin N) (Fin N) ℝ)) =
      (∑ i, α i * (U i i : ℂ)) * φ k := by
  set Δ : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal fun i => U i i with hΔ
  set Nm : Matrix (Fin N) (Fin N) ℝ := U - Δ with hNm
  have hNu : Nm.IsUpperTriangular := hU.sub (Matrix.blockTriangular_diagonal _)
  have hNd : ∀ i, Nm i i = 0 := fun i => by simp [hNm, hΔ]
  set Γ : ℝ → Matrix (Fin N) (Fin N) ℝ := fun t =>
    NormedSpace.exp (t • Δ) * (1 + t • Nm) * (k : Matrix (Fin N) (Fin N) ℝ) with hΓ
  have hΓd : HasDerivAt Γ (U * (k : Matrix (Fin N) (Fin N) ℝ)) 0 := by
    have h1 := hasDerivAt_exp_smul_zero Δ
    have h2 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin N) (Fin N) ℝ) + t • Nm) Nm 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Nm).const_add 1
    have h3 := (h1.mul h2).mul_const (k : Matrix (Fin N) (Fin N) ℝ)
    have e : (Δ * (1 + (0 : ℝ) • Nm) + NormedSpace.exp ((0 : ℝ) • Δ) * Nm) *
        (k : Matrix (Fin N) (Fin N) ℝ) = U * (k : Matrix (Fin N) (Fin N) ℝ) := by
      simp only [zero_smul, add_zero, NormedSpace.exp_zero, one_mul, mul_one]
      rw [hNm, add_sub_cancel]
    exact h3.congr_deriv e
  have hΓ0 : Γ 0 = k := by simp [hΓ]
  have hval : ∀ t : ℝ, Γ t = ((matrixExpUnit N (Matrix.diagonal fun i => t * U i i) *
      ((unipotentLine Nm hNu hNd t : Langlands.GeneralLinear.upperUnipotent N ℝ) :
        Langlands.GeneralLinear N ℝ) * k :
      Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) := by
    intro t
    have hsd : t • Δ = Matrix.diagonal fun i => t * U i i := by
      rw [hΔ, ← Matrix.diagonal_smul]
      rfl
    simp only [Units.val_mul, matrixExpUnit_val, unipotentLine_val, hΓ, hsd]
  have hcomp : (fun t => unitsExtension φ (Γ t)) = fun t : ℝ =>
      Complex.exp (∑ i, α i * ((t * U i i : ℝ) : ℂ)) * φ k := by
    funext t
    rw [hval t, unitsExtension_val, hα]
  have hd1 : HasDerivAt (fun t => unitsExtension φ (Γ t))
      (fderiv ℝ (unitsExtension φ) (k : Matrix (Fin N) (Fin N) ℝ)
        (U * (k : Matrix (Fin N) (Fin N) ℝ))) 0 := by
    have hdiff : HasFDerivAt (unitsExtension φ)
        (fderiv ℝ (unitsExtension φ) (k : Matrix (Fin N) (Fin N) ℝ)) (Γ 0) := by
      rw [hΓ0]
      exact (differentiableAt_unitsExtension hφ (Units.isUnit k)).hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hΓd
  have hlin : HasDerivAt (fun t : ℝ => ∑ i, α i * ((t * U i i : ℝ) : ℂ))
      (∑ i, α i * (U i i : ℂ)) 0 := by
    have e : (fun t : ℝ => ∑ i, α i * ((t * U i i : ℝ) : ℂ)) =
        fun t : ℝ => (t : ℂ) * ∑ i, α i * (U i i : ℂ) := by
      funext t
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [e]
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (∑ i, α i * (U i i : ℂ))
  have hd2 : HasDerivAt (fun t : ℝ =>
      Complex.exp (∑ i, α i * ((t * U i i : ℝ) : ℂ)) * φ k)
      ((∑ i, α i * (U i i : ℂ)) * φ k) 0 := by
    have := hlin.cexp.mul_const (φ k)
    simpa using this
  rw [hcomp] at hd1
  exact hd1.unique hd2

/-! ## Differentiating along the rotations -/

section Rotation

variable {φ : Langlands.GeneralLinear N ℝ → ℂ}

/-- The derivative `dφ̃_{r(θ) g}(W r(θ) g)` of `θ ↦ φ(r(θ) g)`, where `φ̃ = unitsExtension φ`
and `W = rotationGenerator N p`. -/
def rotDeriv (N p : ℕ) (φ : Langlands.GeneralLinear N ℝ → ℂ) (g : Langlands.GeneralLinear N ℝ)
    (θ : ℝ) : ℂ :=
  fderiv ℝ (unitsExtension φ)
    ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)
    (rotationGenerator N p *
      ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ))

theorem hasDerivAt_blockRotation_mul (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) (g : Langlands.GeneralLinear N ℝ) (θ : ℝ) :
    HasDerivAt (fun t => φ (blockRotation N p t * g)) (rotDeriv N p φ g θ) θ := by
  have e : (fun t => φ (blockRotation N p t * g)) =
      fun t => unitsExtension φ (rotMatrix h t * (g : Matrix (Fin N) (Fin N) ℝ)) := by
    funext t
    rw [← blockRotation_val_eq h, ← Units.val_mul, unitsExtension_val]
  rw [e]
  have hu : IsUnit (rotMatrix h θ * (g : Matrix (Fin N) (Fin N) ℝ)) := by
    rw [← blockRotation_val_eq h, ← Units.val_mul]
    exact Units.isUnit _
  have hd := (hasDerivAt_rotMatrix h θ).mul_const (g : Matrix (Fin N) (Fin N) ℝ)
  refine ((differentiableAt_unitsExtension hφ hu).hasFDerivAt.comp_hasDerivAt θ hd).congr_deriv ?_
  simp only [rotDeriv, Units.val_mul, blockRotation_val_eq h, mul_assoc]

theorem continuous_rotDeriv (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ)
    (g : Langlands.GeneralLinear N ℝ) : Continuous (rotDeriv N p φ g) := by
  have hc : Continuous fun θ : ℝ =>
      ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) :=
    Units.continuous_val.comp ((continuous_blockRotation N p).mul continuous_const)
  have hfd := (contDiffOn_unitsExtension hφ).continuousOn_fderiv_of_isOpen
    isOpen_setOf_isUnit_matrix (mod_cast le_top)
  have h1 : Continuous fun θ : ℝ => fderiv ℝ (unitsExtension φ)
      ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) :=
    hfd.comp_continuous hc fun θ => Units.isUnit _
  exact h1.clm_apply (continuous_const.mul hc)

/-- The pointwise decomposition of a left derivative in the direction `r(θ) A g`:
`dφ̃_{r g}(r A g) = (∑ αᵢ Aᵢᵢ - δ (sin² θ u + cos θ sin θ v)) φ(r g) + κ(θ) dφ̃_{r g}(W r g)`. -/
theorem fderiv_blockRotation_mul_mul (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsUpperTriangular) (g : Langlands.GeneralLinear N ℝ)
    (θ : ℝ) :
    fderiv ℝ (unitsExtension φ)
        ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)
        ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A * (g : Matrix (Fin N) (Fin N) ℝ)) =
      (∑ i, α i * (A i i : ℂ) - (α (ia h) - α (ib h)) *
        ((Real.sin θ ^ 2 * (A (ia h) (ia h) - A (ib h) (ib h)) +
          Real.cos θ * Real.sin θ * A (ia h) (ib h) : ℝ) : ℂ)) * φ (blockRotation N p θ * g) +
      (kappa h θ A : ℂ) * rotDeriv N p φ g θ := by
  rw [blockRotation_mul_mul h θ A g, add_mul, map_add, Matrix.smul_mul, map_smul,
    fderiv_upperTriangular_of_isExpEquivariant hφ hα _ (upperPart_isUpperTriangular h θ hA),
    sum_upperPart_diag h θ hA α, Complex.real_smul, rotDeriv]

/-- The Fourier expansion of the coefficients produced by the integration by parts. -/
theorem kappa_fourier_identity (θ : ℝ) (j : ℤ) (S δ : ℂ) (x y v : ℝ) :
    (S - δ * ((Real.sin θ ^ 2 * (x - y) + Real.cos θ * Real.sin θ * v : ℝ) : ℂ)) *
        Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) -
      ((((Real.cos θ ^ 2 - Real.sin θ ^ 2) * (x - y) - 2 * Real.sin θ * Real.cos θ * v : ℝ) : ℂ) *
          Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) +
        ((Real.cos θ * Real.sin θ * (x - y) - Real.sin θ ^ 2 * v : ℝ) : ℂ) *
          (Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (-((j : ℂ) * Complex.I)))) =
      (S - δ * ((x : ℂ) - y) / 2 - Complex.I * v * j / 2) *
          Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) +
        ((x : ℂ) - y + Complex.I * v) / 4 * (δ + j - 2) *
          Complex.exp (-(((j - 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) +
        ((x : ℂ) - y - Complex.I * v) / 4 * (δ - j - 2) *
          Complex.exp (-(((j + 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
  set E := Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) with hE
  have hm : Complex.exp (-(((j - 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) =
      E * (Complex.cos θ ^ 2 - Complex.sin θ ^ 2 + 2 * Complex.cos θ * Complex.sin θ * Complex.I) := by
    have e : -(((j - 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) =
        -((j : ℂ) * (θ : ℂ) * Complex.I) + ((θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, ← hE]
    linear_combination (E * Complex.sin θ ^ 2) * Complex.I_sq
  have hp : Complex.exp (-(((j + 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) =
      E * (Complex.cos θ ^ 2 - Complex.sin θ ^ 2 - 2 * Complex.cos θ * Complex.sin θ * Complex.I) := by
    have e : -(((j + 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) =
        -((j : ℂ) * (θ : ℂ) * Complex.I) + ((-(θ : ℂ)) * Complex.I + (-(θ : ℂ)) * Complex.I) := by
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← hE]
    linear_combination (E * Complex.sin θ ^ 2) * Complex.I_sq
  rw [hm, hp]
  push_cast
  linear_combination (-(E * v * Complex.cos θ * Complex.sin θ * (δ - 2))) * Complex.I_sq +
    (-(E * (δ * ((x : ℂ) - y) + (j : ℂ) * Complex.I * v) / 2)) * Complex.sin_sq_add_cos_sq (θ : ℂ)

/-- **The tridiagonal formula.** For `φ` exp-equivariant with exponents `α` and `A` upper
triangular, the `j`-th block Fourier coefficient of the left derivative in the direction
`r(θ) A g` is a combination of the coefficients of index `j - 2`, `j`, `j + 2` of `φ` at `g`;
here `u = A_pp - A_qq`, `v = A_pq`, `δ = α_p - α_q` with `q = p + 1`. -/
theorem integral_fderiv_blockRotation_mul_mul (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsUpperTriangular) (g : Langlands.GeneralLinear N ℝ)
    (j : ℤ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi,
        fderiv ℝ (unitsExtension φ)
          ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)
          ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A * (g : Matrix (Fin N) (Fin N) ℝ)) *
        Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) =
      (∑ i, α i * (A i i : ℂ) - (α (ia h) - α (ib h)) *
            ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h)) / 2 -
          Complex.I * (A (ia h) (ib h) : ℂ) * j / 2) * blockFourierCoefficient N p j φ g +
        ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h) + Complex.I * A (ia h) (ib h)) / 4 *
          (α (ia h) - α (ib h) + j - 2) * blockFourierCoefficient N p (j - 2) φ g +
        ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h) - Complex.I * A (ia h) (ib h)) / 4 *
          (α (ia h) - α (ib h) - j - 2) * blockFourierCoefficient N p (j + 2) φ g := by
  set x := A (ia h) (ia h) with hx
  set y := A (ib h) (ib h) with hy
  set v := A (ia h) (ib h) with hv
  set S : ℂ := ∑ i, α i * (A i i : ℂ) with hS
  set δ : ℂ := α (ia h) - α (ib h) with hδ
  have hφc : Continuous φ := hφ.continuous
  have hGc : Continuous fun θ : ℝ => φ (blockRotation N p θ * g) :=
    hφc.comp ((continuous_blockRotation N p).mul continuous_const)
  have hG'c := continuous_rotDeriv (p := p) hφ g
  have hec : ∀ k : ℤ, Continuous fun θ : ℝ => Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) :=
    fun k => Complex.continuous_exp.comp (by fun_prop)
  have hsc : Continuous fun θ : ℝ =>
      ((Real.sin θ ^ 2 * (x - y) + Real.cos θ * Real.sin θ * v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have hKc : Continuous fun θ : ℝ => (kappa h θ A : ℂ) :=
    Complex.continuous_ofReal.comp (by unfold kappa; fun_prop)
  have hK'c : Continuous fun θ : ℝ =>
      (((Real.cos θ ^ 2 - Real.sin θ ^ 2) * (x - y) - 2 * Real.sin θ * Real.cos θ * v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have hKd : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => (kappa h θ A : ℂ))
      ((((Real.cos θ ^ 2 - Real.sin θ ^ 2) * (x - y) - 2 * Real.sin θ * Real.cos θ * v : ℝ) :
        ℂ)) θ := by
    intro θ
    have h1 := (((Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)).mul_const (x - y)).sub
      (((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_sin θ)).mul_const v)
    have h2 := h1.congr_of_eventuallyEq (f₁ := fun θ : ℝ => kappa h θ A)
      (Filter.Eventually.of_forall fun t => by
        simp only [kappa, hx, hy, hv, Pi.sub_apply, Pi.mul_apply]; ring)
    exact (h2.congr_deriv (by ring)).ofReal_comp
  have hed : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)))
      (Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (-((j : ℂ) * Complex.I))) θ := by
    intro θ
    have h1 := ((((hasDerivAt_id θ).ofReal_comp).const_mul (j : ℂ)).mul_const Complex.I).neg
    exact (h1.congr_deriv (by simp)).cexp
  have hk0 : kappa h 0 A = 0 := by simp [kappa]
  have hk2 : kappa h (2 * Real.pi) A = 0 := by simp [kappa]
  -- integration by parts
  have ibp : ∫ θ in (0 : ℝ)..2 * Real.pi, (kappa h θ A : ℂ) *
        Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * rotDeriv N p φ g θ =
      -∫ θ in (0 : ℝ)..2 * Real.pi,
        ((((Real.cos θ ^ 2 - Real.sin θ ^ 2) * (x - y) - 2 * Real.sin θ * Real.cos θ * v : ℝ) :
            ℂ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) +
          (kappa h θ A : ℂ) *
            (Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (-((j : ℂ) * Complex.I)))) *
          φ (blockRotation N p θ * g) := by
    have hUd : ∀ θ : ℝ, HasDerivAt
        (fun θ : ℝ => (kappa h θ A : ℂ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)))
        ((((Real.cos θ ^ 2 - Real.sin θ ^ 2) * (x - y) - 2 * Real.sin θ * Real.cos θ * v : ℝ) :
            ℂ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) +
          (kappa h θ A : ℂ) *
            (Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (-((j : ℂ) * Complex.I)))) θ :=
      fun θ => (hKd θ).mul (hed θ)
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hUd θ)
      (fun θ _ => hasDerivAt_blockRotation_mul h hφ g θ)
      (((hK'c.mul (hec j)).add (hKc.mul ((hec j).mul continuous_const))).intervalIntegrable _ _)
      (hG'c.intervalIntegrable _ _), hk0, hk2]
    simp
  have hpt : ∀ θ : ℝ,
      fderiv ℝ (unitsExtension φ)
          ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)
          ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A * (g : Matrix (Fin N) (Fin N) ℝ)) *
        Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) =
      (S - δ * ((Real.sin θ ^ 2 * (x - y) + Real.cos θ * Real.sin θ * v : ℝ) : ℂ)) *
          φ (blockRotation N p θ * g) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) +
        (kappa h θ A : ℂ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) *
          rotDeriv N p φ g θ := by
    intro θ
    rw [fderiv_blockRotation_mul_mul h hφ hα hA g θ]
    ring
  have int1 : IntervalIntegrable (fun θ : ℝ =>
      (S - δ * ((Real.sin θ ^ 2 * (x - y) + Real.cos θ * Real.sin θ * v : ℝ) : ℂ)) *
          φ (blockRotation N p θ * g) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (((continuous_const.sub (continuous_const.mul hsc)).mul hGc).mul (hec j)).intervalIntegrable _ _
  have int2 : IntervalIntegrable (fun θ : ℝ =>
      (kappa h θ A : ℂ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * rotDeriv N p φ g θ)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    ((hKc.mul (hec j)).mul hG'c).intervalIntegrable _ _
  have int3 : IntervalIntegrable (fun θ : ℝ =>
      ((((Real.cos θ ^ 2 - Real.sin θ ^ 2) * (x - y) - 2 * Real.sin θ * Real.cos θ * v : ℝ) :
            ℂ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) +
          (kappa h θ A : ℂ) *
            (Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (-((j : ℂ) * Complex.I)))) *
          φ (blockRotation N p θ * g))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (((hK'c.mul (hec j)).add (hKc.mul ((hec j).mul continuous_const))).mul hGc).intervalIntegrable
      _ _
  have hpt2 : ∀ θ : ℝ,
      (S - δ * ((Real.sin θ ^ 2 * (x - y) + Real.cos θ * Real.sin θ * v : ℝ) : ℂ)) *
          φ (blockRotation N p θ * g) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) -
        ((((Real.cos θ ^ 2 - Real.sin θ ^ 2) * (x - y) - 2 * Real.sin θ * Real.cos θ * v : ℝ) :
              ℂ) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) +
            (kappa h θ A : ℂ) *
              (Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (-((j : ℂ) * Complex.I)))) *
          φ (blockRotation N p θ * g) =
      (S - δ * ((x : ℂ) - y) / 2 - Complex.I * v * j / 2) *
          (φ (blockRotation N p θ * g) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))) +
        ((x : ℂ) - y + Complex.I * v) / 4 * (δ + j - 2) *
          (φ (blockRotation N p θ * g) *
            Complex.exp (-(((j - 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) +
        ((x : ℂ) - y - Complex.I * v) / 4 * (δ - j - 2) *
          (φ (blockRotation N p θ * g) *
            Complex.exp (-(((j + 2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) := by
    intro θ
    have key := kappa_fourier_identity θ j S δ x y v
    rw [kappa]
    linear_combination φ (blockRotation N p θ * g) * key
  have f1 := (intervalIntegrable_blockFourier hφc p j g 0 (2 * Real.pi)).const_mul
    (S - δ * ((x : ℂ) - y) / 2 - Complex.I * v * j / 2)
  have f2 := (intervalIntegrable_blockFourier hφc p (j - 2) g 0 (2 * Real.pi)).const_mul
    (((x : ℂ) - y + Complex.I * v) / 4 * (δ + j - 2))
  have f3 := (intervalIntegrable_blockFourier hφc p (j + 2) g 0 (2 * Real.pi)).const_mul
    (((x : ℂ) - y - Complex.I * v) / 4 * (δ - j - 2))
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_add int1 int2,
    ibp, ← sub_eq_add_neg, ← intervalIntegral.integral_sub int1 int3,
    intervalIntegral.integral_congr (fun θ _ => hpt2 θ), intervalIntegral.integral_add (f1.add f2) f3,
    intervalIntegral.integral_add f1 f2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [blockFourierCoefficient]

/-- **The tridiagonal formula for a right derivative.** If `g X = A g` with `A` upper
triangular, the `j`-th block Fourier coefficient at `g` of the right derivative `R_X φ` is the
combination of the coefficients of index `j - 2`, `j`, `j + 2` of `φ` at `g` given by
`integral_fderiv_blockRotation_mul_mul`. For `g = 1` the condition is `X = A`. -/
theorem blockFourierCoefficient_rightDerivative (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    {A X : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsUpperTriangular) (g : Langlands.GeneralLinear N ℝ)
    (hX : (g : Matrix (Fin N) (Fin N) ℝ) * X = A * (g : Matrix (Fin N) (Fin N) ℝ)) (j : ℤ) :
    blockFourierCoefficient N p j (rightDerivative (matrixModel ℝ N) X φ) g =
      (∑ i, α i * (A i i : ℂ) - (α (ia h) - α (ib h)) *
            ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h)) / 2 -
          Complex.I * (A (ia h) (ib h) : ℂ) * j / 2) * blockFourierCoefficient N p j φ g +
        ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h) + Complex.I * A (ia h) (ib h)) / 4 *
          (α (ia h) - α (ib h) + j - 2) * blockFourierCoefficient N p (j - 2) φ g +
        ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h) - Complex.I * A (ia h) (ib h)) / 4 *
          (α (ia h) - α (ib h) - j - 2) * blockFourierCoefficient N p (j + 2) φ g := by
  refine Eq.trans ?_ (integral_fderiv_blockRotation_mul_mul h hφ hα hA g j)
  unfold blockFourierCoefficient
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have e : ((blockRotation N p θ * g : Langlands.GeneralLinear N ℝ) :
      Matrix (Fin N) (Fin N) ℝ) * X =
      (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A * (g : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Units.val_mul, mul_assoc, hX, ← mul_assoc]
  rw [rightDerivative_eq_fderiv hφ, e]

/-- **The tridiagonal formula along a path.** If `γ` is a `C¹` path in `GL_N(ℝ)` with
`γ'(s₀) = A γ(s₀)` for an upper triangular `A`, then `s ↦ Φ_j(φ)(γ s)` has at `s₀` the
derivative given by `integral_fderiv_blockRotation_mul_mul` at `g = γ s₀`. -/
theorem hasDerivAt_blockFourierCoefficient_comp (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    {γ : ℝ → Langlands.GeneralLinear N ℝ}
    (hγ : ContDiff ℝ 1 fun s => (γ s : Matrix (Fin N) (Fin N) ℝ)) {s₀ : ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsUpperTriangular)
    (hγ' : HasDerivAt (fun s => (γ s : Matrix (Fin N) (Fin N) ℝ))
      (A * (γ s₀ : Matrix (Fin N) (Fin N) ℝ)) s₀) (j : ℤ) :
    HasDerivAt (fun s => blockFourierCoefficient N p j φ (γ s))
      ((∑ i, α i * (A i i : ℂ) - (α (ia h) - α (ib h)) *
            ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h)) / 2 -
          Complex.I * (A (ia h) (ib h) : ℂ) * j / 2) * blockFourierCoefficient N p j φ (γ s₀) +
        ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h) + Complex.I * A (ia h) (ib h)) / 4 *
          (α (ia h) - α (ib h) + j - 2) * blockFourierCoefficient N p (j - 2) φ (γ s₀) +
        ((A (ia h) (ia h) : ℂ) - A (ib h) (ib h) - Complex.I * A (ia h) (ib h)) / 4 *
          (α (ia h) - α (ib h) - j - 2) * blockFourierCoefficient N p (j + 2) φ (γ s₀)) s₀ := by
  rw [← integral_fderiv_blockRotation_mul_mul h hφ hα hA (γ s₀) j]
  set Φ : ℝ × ℝ → ℂ := fun q => unitsExtension φ (rotMatrix h q.2 *
      (γ q.1 : Matrix (Fin N) (Fin N) ℝ)) * Complex.exp (-((j : ℂ) * (q.2 : ℂ) * Complex.I))
    with hΦ
  have hval : ∀ (s θ : ℝ), rotMatrix h θ * (γ s : Matrix (Fin N) (Fin N) ℝ) =
      ((blockRotation N p θ * γ s : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) := by
    intro s θ
    rw [Units.val_mul, blockRotation_val_eq h]
  have hrot : ContDiff ℝ 1 fun q : ℝ × ℝ => rotMatrix h q.2 := by
    unfold rotMatrix
    fun_prop
  have hM : ContDiff ℝ 1 fun q : ℝ × ℝ =>
      rotMatrix h q.2 * (γ q.1 : Matrix (Fin N) (Fin N) ℝ) :=
    hrot.mul (hγ.comp contDiff_fst)
  have hU : ContDiff ℝ 1 fun q : ℝ × ℝ => unitsExtension φ (rotMatrix h q.2 *
      (γ q.1 : Matrix (Fin N) (Fin N) ℝ)) :=
    ((contDiffOn_unitsExtension hφ).of_le (mod_cast le_top)).comp_contDiff hM fun q => by
      rw [hval]
      exact Units.isUnit _
  have hθ : ContDiff ℝ 1 fun q : ℝ × ℝ => (q.2 : ℂ) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have hE : ContDiff ℝ 1 fun q : ℝ × ℝ => Complex.exp (-((j : ℂ) * (q.2 : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((contDiff_const.mul hθ).mul contDiff_const).neg
  have hΦc : ContDiff ℝ 1 Φ := hU.mul hE
  have hΦ' : ∀ θ : ℝ, HasDerivAt (fun s => Φ (s, θ))
      (fderiv ℝ (unitsExtension φ)
          ((blockRotation N p θ * γ s₀ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)
          ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A *
            (γ s₀ : Matrix (Fin N) (Fin N) ℝ)) *
        Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))) s₀ := by
    intro θ
    have hd := hγ'.const_mul (rotMatrix h θ)
    have hu : IsUnit (rotMatrix h θ * (γ s₀ : Matrix (Fin N) (Fin N) ℝ)) := by
      rw [hval]
      exact Units.isUnit _
    have h1 := ((differentiableAt_unitsExtension hφ hu).hasFDerivAt.comp_hasDerivAt s₀ hd).mul_const
      (Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)))
    refine h1.congr_deriv ?_
    rw [hval, blockRotation_val_eq h, ← mul_assoc (rotMatrix h θ) A]
  have hd := hasDerivAt_intervalIntegral_of_contDiff hΦc hΦ' 0 (2 * Real.pi)
  refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  unfold blockFourierCoefficient
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [hΦ, hval, unitsExtension_val]

end Rotation

end RealBlockDerivative

end Langlands.Archimedean
