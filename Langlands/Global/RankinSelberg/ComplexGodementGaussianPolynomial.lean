import Langlands.Global.RankinSelberg.ComplexGodementFourier
import Langlands.Global.RankinSelberg.ComplexGodementKFinite
import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration
import Langlands.Global.Hecke.MixedSpaceFourier
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Compact-finite Gaussian polynomial tests on complex matrices -/

noncomputable section

open scoped ContDiff Matrix.Norms.Operator SchwartzMap
open MvPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial

open Langlands.Archimedean ComplexGodement
open ComplexGodementFourier (curryLinearEquiv)
open Langlands.Global.Hecke (exists_exp_neg_mul_sq_le_rpow)
open Langlands.Archimedean.ComplexLastRowIntegral (sqNorm_vecMul)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (mul_conjTranspose_one)

variable {m n : ℕ}
private abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

/-- An entry and a selector for its real (`false`) or imaginary (`true`) coordinate. -/
abbrev Coordinates (m n : ℕ) := Fin m × Fin n × Bool

/-- The selected real or imaginary part, included into ℂ. -/
def coordinatePartCLM (b : Bool) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (if b then Complex.imCLM else Complex.reCLM)

/-- Real coordinates of a complex matrix, regarded as complex scalars. -/
def coordinates (A : Mat m n) (v : Coordinates m n) : ℂ := coordinatePartCLM v.2.2 (A v.1 v.2.1)

@[simp] theorem coordinates_re (A : Mat m n) (i : Fin m) (j : Fin n) :
    coordinates A (i, j, false) = ((A i j).re : ℂ) := rfl

@[simp] theorem coordinates_im (A : Mat m n) (i : Fin m) (j : Fin n) :
    coordinates A (i, j, true) = ((A i j).im : ℂ) := rfl

private def coordCLM (v : Coordinates m n) : Mat m n →L[ℝ] ℂ :=
  coordinatePartCLM v.2.2 |>.comp
    ({ toFun := fun A => A v.1 v.2.1
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : Mat m n →ₗ[ℝ] ℂ).toContinuousLinearMap

/-- Evaluating a polynomial on continuous real-linear coordinates has temperate growth. -/
theorem eval_hasTemperateGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (c : ι → E →L[ℝ] ℂ) (p : MvPolynomial ι ℂ) :
    (fun x => eval (fun i => c i x) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [eval_C] using (Function.HasTemperateGrowth.const (E := E) a)
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, eval_X]
      exact hp.mul (c i).hasTemperateGrowth

/-- The radial Gaussian on a real inner product space. -/
def radialGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℝ) where
  toFun x := Real.exp (-‖x‖ ^ 2)
  smooth' := Real.contDiff_exp.comp <| (show (fun x : E => -‖x‖ ^ 2).HasTemperateGrowth by
    fun_prop).1
  decay' k n := by
    let Q : E → ℝ := fun x => -‖x‖ ^ 2
    have hQ : Q.HasTemperateGrowth := by dsimp [Q]; fun_prop
    obtain ⟨l, C, _, hderiv⟩ := hQ.norm_iteratedFDeriv_le_uniform n
    obtain ⟨B, _, hgauss⟩ := exists_exp_neg_mul_sq_le_rpow (c := 1)
      one_pos ((k + l * n : ℕ) : ℝ)
    let A := max 1 C
    refine ⟨(n.factorial : ℝ) * A ^ n * B, fun x => ?_⟩
    let R := 1 + ‖x‖
    have hR : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg x)
    have hA : 1 ≤ A := le_max_left _ _
    have hD : 1 ≤ A * R ^ l := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hR)
    have hbound := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := Q) (n := n)
      Real.contDiff_exp hQ.1 (by exact_mod_cast le_top) x
      (C := Real.exp (Q x)) (D := A * R ^ l)
      (fun i _ => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
          Real.iter_deriv_exp, Real.norm_eq_abs, Real.abs_exp])
      (fun i hi hin => (hderiv i hin x).trans <|
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans
          (le_self_pow₀ hD (by omega)))
    have hdecay : R ^ (k + l * n) * Real.exp (Q x) ≤ B := by
      have h := hgauss ‖x‖ (norm_nonneg x)
      simp only [one_mul] at h
      change Real.exp (Q x) ≤ B * R ^ (-((k + l * n : ℕ) : ℝ)) at h
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, le_mul_inv_iff₀ (by positivity)] at h
      rwa [mul_comm]
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ Q) x‖ ≤ _
    calc
      _ ≤ R ^ k * ((n.factorial : ℝ) * Real.exp (Q x) * (A * R ^ l) ^ n) := by
            gcongr
            exact le_add_of_nonneg_left zero_le_one
      _ = (n.factorial : ℝ) * A ^ n * (R ^ (k + l * n) * Real.exp (Q x)) := by
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      _ ≤ (n.factorial : ℝ) * A ^ n * B := mul_le_mul_of_nonneg_left hdecay (by positivity)

private def matrixEuclidean (m n : ℕ) : Mat m n ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  ((curryLinearEquiv (Fin m) (Fin n) ℝ ℂ).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).toContinuousLinearEquiv

/-- The squared sum of the absolute values of all matrix entries. -/
def matrixSqNorm (A : Mat m n) : ℝ := ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ ^ 2

private theorem matrixEuclidean_norm_sq (A : Mat m n) :
    ‖matrixEuclidean m n A‖ ^ 2 = matrixSqNorm A := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- The scalar matrix Gaussian with variance parameter in the exponent equal to 1. -/
def matrixGaussian (A : Mat m n) : ℂ := (Real.exp (-matrixSqNorm A) : ℂ)

private def matrixGaussianSchwartz (m n : ℕ) : 𝓢(Mat m n, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (matrixEuclidean m n)
    (radialGaussian.postcompCLM Complex.ofRealCLM)

private theorem matrixGaussianSchwartz_apply (A : Mat m n) :
    matrixGaussianSchwartz m n A = matrixGaussian A := by
  change (Real.exp (-‖matrixEuclidean m n A‖ ^ 2) : ℂ) = _
  rw [matrixEuclidean_norm_sq, matrixGaussian]

/-- Complex polynomial in the real coordinates times the fixed matrix Gaussian. -/
def gaussianPolynomial (p : MvPolynomial (Coordinates m n) ℂ) : 𝓢(Mat m n, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun A => eval (coordinates A) p) (matrixGaussianSchwartz m n)

@[simp] theorem gaussianPolynomial_apply (p : MvPolynomial (Coordinates m n) ℂ) (A : Mat m n) :
    gaussianPolynomial p A = eval (coordinates A) p * matrixGaussian A := by
  have hp : (fun A => eval (coordinates A) p).HasTemperateGrowth := eval_hasTemperateGrowth coordCLM p
  rw [gaussianPolynomial, SchwartzMap.smulLeftCLM_apply_apply hp, smul_eq_mul,
    matrixGaussianSchwartz_apply]

/-- Right multiplication by a unitary matrix preserves the scalar Gaussian. -/
theorem matrixGaussian_mul_unitary (A : Mat m n) (k : unitaryCompact ℂ n) :
    matrixGaussian (A * k.val.val) = matrixGaussian A := by
  unfold matrixGaussian matrixSqNorm
  congr 2
  apply congrArg Neg.neg
  exact Finset.sum_congr rfl fun i _ => sqNorm_vecMul (mul_conjTranspose_one k) (A i)

/-- Substituting the coordinates of right multiplication, whose entries are real-linear. -/
private def translateVariable (K : Mat n n) (v : Coordinates m n) :
    MvPolynomial (Coordinates m n) ℂ :=
  ∑ l : Fin n,
    (C (coordinatePartCLM v.2.2 (K l v.2.1)) * X (v.1, l, false) +
      C (coordinatePartCLM v.2.2 (Complex.I * K l v.2.1)) * X (v.1, l, true))

private theorem coordinatePartCLM_mul (b : Bool) (z w : ℂ) :
    coordinatePartCLM b (z * w) = coordinatePartCLM b w * (z.re : ℂ) +
      coordinatePartCLM b (Complex.I * w) * (z.im : ℂ) := by
  calc
    _ = coordinatePartCLM b ((z.re : ℂ) * w + (z.im : ℂ) * (Complex.I * w)) := by
      congr 1
      rw [← mul_assoc, ← add_mul, Complex.re_add_im]
    _ = _ := by
      change coordinatePartCLM b (z.re • w + z.im • (Complex.I * w)) = _
      rw [map_add, (coordinatePartCLM b).map_smul, (coordinatePartCLM b).map_smul]
      simp only [Complex.real_smul]
      ring

private theorem eval_translateVariable (A : Mat m n) (K : Mat n n) (v : Coordinates m n) :
    eval (coordinates A) (translateVariable K v) = coordinates (A * K) v := by
  rcases v with ⟨i, j, b⟩
  simp only [translateVariable, map_sum, map_add, map_mul, eval_C, eval_X,
    coordinates_re, coordinates_im]
  change _ = coordinatePartCLM b ((A * K) i j)
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun l _ => (coordinatePartCLM_mul b _ _).symm

private theorem totalDegree_translateVariable (K : Mat n n) (v : Coordinates m n) :
    (translateVariable K v).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro l _
  refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;>
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

private def weightedEval (m n : ℕ) : MvPolynomial (Coordinates m n) ℂ →ₗ[ℂ] (Mat m n → ℂ) where
  toFun p A := eval (coordinates A) p * matrixGaussian A
  map_add' p q := by ext A; simp [add_mul]
  map_smul' a p := by
    ext A
    simp [MvPolynomial.smul_eq_C_mul, mul_assoc]

/-- A right unitary translate has a polynomial representative of no larger total degree. -/
theorem exists_gaussianPolynomial_mul_unitary (p : MvPolynomial (Coordinates m n) ℂ)
    (k : unitaryCompact ℂ n) :
    ∃ q : MvPolynomial (Coordinates m n) ℂ,
      q.totalDegree ≤ p.totalDegree ∧
      ∀ A : Mat m n, gaussianPolynomial p (A * k.val.val) = gaussianPolynomial q A := by
  refine ⟨bind₁ (translateVariable k.val.val) p,
    totalDegree_bind₁_le _ (totalDegree_translateVariable k.val.val) p, fun A => ?_⟩
  rw [gaussianPolynomial_apply, gaussianPolynomial_apply, matrixGaussian_mul_unitary]
  congr 1
  change aeval (coordinates (A * k.val.val)) p =
    aeval (coordinates A) (bind₁ (translateVariable k.val.val) p)
  rw [aeval_bind₁]
  simp_rw [show ∀ i, aeval (coordinates A) (translateVariable k.val.val i) =
      coordinates (A * k.val.val) i from eval_translateVariable A k.val.val]

/-- Right unitary translates of a polynomial Gaussian on any rectangular matrix space
span a finite-dimensional space. -/
theorem finiteDimensional_rightTranslate_gaussianPolynomial
    (p : MvPolynomial (Coordinates m n) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      fun A : Mat m n => gaussianPolynomial p (A * k.val.val))) := by
  let V := restrictTotalDegree (Coordinates m n) ℂ p.totalDegree
  let L := (weightedEval m n).comp V.subtype
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  let q := bind₁ (translateVariable k.val.val) p
  have hq : q ∈ V := (mem_restrictTotalDegree _ _ _).mpr <|
    totalDegree_bind₁_le _ (totalDegree_translateVariable k.val.val) p
  refine ⟨⟨q, hq⟩, ?_⟩
  funext A
  change eval (coordinates A) q * matrixGaussian A = gaussianPolynomial p (A * k.val.val)
  rw [gaussianPolynomial_apply, matrixGaussian_mul_unitary]
  congr 1
  change aeval (coordinates A) q = aeval (coordinates (A * k.val.val)) p
  rw [show q = bind₁ (translateVariable k.val.val) p from rfl, aeval_bind₁]
  simp_rw [show ∀ i, aeval (coordinates A) (translateVariable k.val.val i) =
      coordinates (A * k.val.val) i from eval_translateVariable A k.val.val]

/-- In the Godement rectangle the right action is `translateTest`. -/
theorem finiteDimensional_translateTest_gaussianPolynomial
    (p : MvPolynomial (Coordinates m (m + 1)) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ (m + 1) =>
      translateTest k.val (gaussianPolynomial p))) :=
  finiteDimensional_rightTranslate_gaussianPolynomial p

/-- The span of right unitary translates of each fixed Gaussian-polynomial test
is finite dimensional. -/
def ComplexGodementGaussianPolynomialStatement : Prop :=
  ∀ (m : ℕ) (p : MvPolynomial (Coordinates m (m + 1)) ℂ),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ (m + 1) =>
      translateTest k.val (gaussianPolynomial p)))

theorem complexGodementGaussianPolynomial : ComplexGodementGaussianPolynomialStatement :=
  fun _ => finiteDimensional_translateTest_gaussianPolynomial

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial
