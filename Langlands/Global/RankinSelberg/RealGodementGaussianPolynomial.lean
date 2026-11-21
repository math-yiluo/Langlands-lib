import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Polynomial Gaussian tests on real rectangular matrices -/

noncomputable section

open scoped ContDiff Matrix.Norms.Operator SchwartzMap
open MvPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodementGaussianPolynomial

open Langlands.Archimedean
open ComplexGodementGaussianPolynomial (eval_hasTemperateGrowth radialGaussian)
open ComplexGodementFourier (curryLinearEquiv)

variable {m n : ℕ}

/-- The entry coordinates of a real `m × n` matrix. -/
abbrev Coordinates (m n : ℕ) := Fin m × Fin n

/-- The entries of a real matrix, regarded as complex scalars. -/
def coordinates (A : Matrix (Fin m) (Fin n) ℝ) (v : Coordinates m n) : ℂ := (A v.1 v.2 : ℂ)

@[simp] theorem coordinates_apply (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    coordinates A (i, j) = (A i j : ℂ) := rfl

private def entryLinear (v : Coordinates m n) : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun A := A v.1 v.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def coordCLM (v : Coordinates m n) : Matrix (Fin m) (Fin n) ℝ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (entryLinear v).toContinuousLinearMap

private theorem coordCLM_apply (v : Coordinates m n) (A : Matrix (Fin m) (Fin n) ℝ) :
    coordCLM v A = coordinates A v := rfl

/-- Evaluation of a polynomial in the entries has temperate growth. -/
theorem eval_coordinates_hasTemperateGrowth (p : MvPolynomial (Coordinates m n) ℂ) :
    (fun A : Matrix (Fin m) (Fin n) ℝ => eval (coordinates A) p).HasTemperateGrowth :=
  eval_hasTemperateGrowth coordCLM p

/-- The sum of the squares of all entries. -/
def matrixSqNorm (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2

theorem matrixSqNorm_nonneg (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ matrixSqNorm A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The entries of a real matrix as a Euclidean vector. -/
def matrixEuclidean (m n : ℕ) :
    Matrix (Fin m) (Fin n) ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
  ((curryLinearEquiv (Fin m) (Fin n) ℝ ℝ).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℝ)).symm).toContinuousLinearEquiv

theorem matrixEuclidean_norm_sq (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖matrixEuclidean m n A‖ ^ 2 = matrixSqNorm A := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change ‖A i j‖ ^ 2 = A i j ^ 2
  rw [Real.norm_eq_abs, sq_abs]

private def scaledEuclidean (m n : ℕ) (t : ℝ) (ht : 0 < t) :
    Matrix (Fin m) (Fin n) ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
  (((curryLinearEquiv (Fin m) (Fin n) ℝ ℝ).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℝ)).symm).trans
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin m × Fin n)) (Real.sqrt t)
      (Real.sqrt_pos.mpr ht).ne')).toContinuousLinearEquiv

private theorem scaledEuclidean_norm_sq (t : ℝ) (ht : 0 < t) (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖scaledEuclidean m n t ht A‖ ^ 2 = t * matrixSqNorm A := by
  change ‖Real.sqrt t • matrixEuclidean m n A‖ ^ 2 = _
  rw [norm_smul, mul_pow, matrixEuclidean_norm_sq, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht.le]

/-- The scalar Gaussian `exp(-t ∑ Aᵢⱼ²)` as a Schwartz test, for `t > 0`. -/
def scaledGaussian (m n : ℕ) (t : ℝ) (ht : 0 < t) : 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (scaledEuclidean m n t ht)
    (radialGaussian.postcompCLM Complex.ofRealCLM)

theorem scaledGaussian_apply (t : ℝ) (ht : 0 < t) (A : Matrix (Fin m) (Fin n) ℝ) :
    scaledGaussian m n t ht A = (Real.exp (-(t * matrixSqNorm A)) : ℂ) := by
  change (Real.exp (-‖scaledEuclidean m n t ht A‖ ^ 2) : ℂ) = _
  rw [scaledEuclidean_norm_sq]

/-- The scalar matrix Gaussian `exp(-∑ Aᵢⱼ²)`. -/
def matrixGaussian (A : Matrix (Fin m) (Fin n) ℝ) : ℂ := (Real.exp (-matrixSqNorm A) : ℂ)

/-- A complex polynomial in the entries times the matrix Gaussian. -/
def gaussianPolynomial (p : MvPolynomial (Coordinates m n) ℂ) : 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun A => eval (coordinates A) p) (scaledGaussian m n 1 one_pos)

@[simp] theorem gaussianPolynomial_apply (p : MvPolynomial (Coordinates m n) ℂ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    gaussianPolynomial p A = eval (coordinates A) p * matrixGaussian A := by
  rw [gaussianPolynomial, SchwartzMap.smulLeftCLM_apply_apply
    (eval_coordinates_hasTemperateGrowth p), smul_eq_mul, scaledGaussian_apply, one_mul]
  rfl

theorem gaussianPolynomial_add (p q : MvPolynomial (Coordinates m n) ℂ) :
    gaussianPolynomial (p + q) = gaussianPolynomial p + gaussianPolynomial q := by
  ext A
  simp only [gaussianPolynomial_apply, map_add, add_mul, add_apply]

theorem gaussianPolynomial_smul (c : ℂ) (p : MvPolynomial (Coordinates m n) ℂ) :
    gaussianPolynomial (c • p) = c • gaussianPolynomial p := by
  ext A
  simp only [gaussianPolynomial_apply, MvPolynomial.smul_eval, smul_apply,
    smul_eq_mul, mul_assoc]

/-- The polynomial Gaussian tests as a complex-linear map. -/
def gaussianPolynomialLinear (m n : ℕ) :
    MvPolynomial (Coordinates m n) ℂ →ₗ[ℂ] 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ) where
  toFun := gaussianPolynomial
  map_add' := gaussianPolynomial_add
  map_smul' := gaussianPolynomial_smul

/-- The half-strength Gaussian `exp(-∑ Aᵢⱼ² / 2)`. -/
def halfGaussian (m n : ℕ) : 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ) :=
  scaledGaussian m n (1 / 2) (by norm_num)

theorem halfGaussian_apply (A : Matrix (Fin m) (Fin n) ℝ) :
    halfGaussian m n A = (Real.exp (-matrixSqNorm A / 2) : ℂ) := by
  rw [halfGaussian, scaledGaussian_apply]
  congr 2
  ring

/-- Every polynomial Gaussian test is a Schwartz function times the half-strength Gaussian. -/
theorem exists_gaussianPolynomial_half_factor (p : MvPolynomial (Coordinates m n) ℂ) :
    ∃ Ψ : 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ), ∀ A,
      gaussianPolynomial p A = Ψ A * halfGaussian m n A := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun A => eval (coordinates A) p) (halfGaussian m n),
    fun A => ?_⟩
  rw [gaussianPolynomial_apply, SchwartzMap.smulLeftCLM_apply_apply
    (eval_coordinates_hasTemperateGrowth p), smul_eq_mul, halfGaussian_apply, matrixGaussian,
    mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-- A real linear functional on matrices as a linear polynomial in the entries. -/
def realLinearPolynomial (L : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    MvPolynomial (Coordinates m n) ℂ :=
  ∑ i, ∑ j, C (L (Matrix.single i j 1) : ℂ) * X (i, j)

theorem eval_realLinearPolynomial (L : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    eval (coordinates A) (realLinearPolynomial L) = (L A : ℂ) := by
  have hsum : (∑ i, ∑ j, A i j • Matrix.single i j (1 : ℝ)) = A := by
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_).trans
      (Matrix.sum_sum_single A)
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_rhs => rw [← hsum]
  simp only [realLinearPolynomial, map_sum, map_mul, eval_C, eval_X, coordinates_apply,
    map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem totalDegree_realLinearPolynomial (L : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    (realLinearPolynomial L).totalDegree ≤ 1 := by
  refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun j _ => ?_
  exact (totalDegree_mul _ _).trans (by simp)

private theorem totalDegree_bind₁_le {ι κ : Type*} (f : ι → MvPolynomial κ ℂ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial ι ℂ) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun d hd => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans
    (le_totalDegree hd))
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))

/-- Right multiplication by an orthogonal matrix preserves the sum of squares. -/
theorem matrixSqNorm_mul_orthogonal (A : Matrix (Fin m) (Fin n) ℝ)
    (k : unitaryCompact ℝ n) : matrixSqNorm (A * k.val.val) = matrixSqNorm A := by
  have hk : k.val.val * k.val.val.transpose = 1 := by
    have h := Unitary.mul_star_self_of_mem k.2
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using h
  have htrace (B : Matrix (Fin m) (Fin n) ℝ) : matrixSqNorm B = Matrix.trace (B * B.transpose) := by
    simp only [matrixSqNorm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      sq]
  rw [htrace, htrace, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k.val.val,
    hk, Matrix.one_mul]

theorem matrixGaussian_mul_orthogonal (A : Matrix (Fin m) (Fin n) ℝ)
    (k : unitaryCompact ℝ n) : matrixGaussian (A * k.val.val) = matrixGaussian A := by
  rw [matrixGaussian, matrixGaussian, matrixSqNorm_mul_orthogonal]

theorem halfGaussian_mul_orthogonal (A : Matrix (Fin m) (Fin n) ℝ)
    (k : unitaryCompact ℝ n) : halfGaussian m n (A * k.val.val) = halfGaussian m n A := by
  rw [halfGaussian_apply, halfGaussian_apply, matrixSqNorm_mul_orthogonal]

/-- Right multiplication by a matrix acts on polynomial Gaussian tests by a linear
substitution in the entries, which does not raise the total degree. -/
theorem exists_rightTranslate_gaussianPolynomial (p : MvPolynomial (Coordinates m n) ℂ)
    (k : unitaryCompact ℝ n) :
    ∃ q : MvPolynomial (Coordinates m n) ℂ, q.totalDegree ≤ p.totalDegree ∧
      ∀ A, gaussianPolynomial p (A * k.val.val) = gaussianPolynomial q A := by
  let L (v : Coordinates m n) : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    (entryLinear v).comp (_root_.mulRightLinearMap (Fin m) ℝ k.val.val)
  let q (v : Coordinates m n) := realLinearPolynomial (L v)
  refine ⟨bind₁ q p, totalDegree_bind₁_le q (fun v => totalDegree_realLinearPolynomial _) p,
    fun A => ?_⟩
  rw [gaussianPolynomial_apply, gaussianPolynomial_apply, matrixGaussian_mul_orthogonal]
  congr 1
  change aeval (coordinates (A * k.val.val)) p = aeval (coordinates A) (bind₁ q p)
  rw [aeval_bind₁]
  have hq (v : Coordinates m n) : aeval (coordinates A) (q v) = coordinates (A * k.val.val) v :=
    eval_realLinearPolynomial (L v) A
  simp_rw [hq]

/-- Right orthogonal translates of a polynomial Gaussian test lie in the finite-dimensional
image of the polynomials of at most the same total degree. -/
theorem rightTranslate_mem_range (p : MvPolynomial (Coordinates m n) ℂ)
    (k : unitaryCompact ℝ n) :
    ∃ q ∈ restrictTotalDegree (Coordinates m n) ℂ p.totalDegree,
      ∀ A, gaussianPolynomial p (A * k.val.val) = gaussianPolynomial q A := by
  obtain ⟨q, hq, hA⟩ := exists_rightTranslate_gaussianPolynomial p k
  exact ⟨q, (mem_restrictTotalDegree _ _ _).mpr hq, hA⟩

/-- The polynomial Gaussian tests are preserved by right orthogonal translation with
no increase of total degree, and each is a Schwartz function times the half-strength
Gaussian. -/
def RealGodementGaussianPolynomialStatement : Prop :=
  ∀ (m n : ℕ) (p : MvPolynomial (Coordinates m n) ℂ),
    (∀ k : unitaryCompact ℝ n, ∃ q : MvPolynomial (Coordinates m n) ℂ,
      q.totalDegree ≤ p.totalDegree ∧
        ∀ A, gaussianPolynomial p (A * k.val.val) = gaussianPolynomial q A) ∧
    ∃ Ψ : 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ), ∀ A,
      gaussianPolynomial p A = Ψ A * halfGaussian m n A

theorem realGodementGaussianPolynomial : RealGodementGaussianPolynomialStatement :=
  fun _ _ p => ⟨exists_rightTranslate_gaussianPolynomial p,
    exists_gaussianPolynomial_half_factor p⟩

end Langlands.Global.RankinSelbergGlobal.RealGodementGaussianPolynomial
