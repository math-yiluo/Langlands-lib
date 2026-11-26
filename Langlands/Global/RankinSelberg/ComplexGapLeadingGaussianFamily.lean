import Langlands.Global.RankinSelberg.ComplexGapSquareReflection
import Langlands.Global.RankinSelberg.ComplexGodementStandardGaussians

/-! # Gaussian square tests on the retained gap chart -/

noncomputable section

open MvPolynomial
open scoped Matrix Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingCompact

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (mul_conjTranspose_one)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.GeneralLinear (scalar)
open ComplexGapDualChart (retainedTail)
open ComplexGapLeadingFourier (stackRows stackRows_left stackRows_right)
open ComplexGapSquareReflection (leadingSquareTest leadingSquareTest_apply)
open ComplexGapTriangularChart (Outer)
open ComplexGapUnitDeterminant (normalizingScalar leadingScalar)
open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinates_re coordinates_im coordinatePartCLM matrixSqNorm matrixGaussian
  matrixGaussian_mul_unitary standardMatrixTest standardMatrixTest_apply scalePolynomial)
open ComplexSquareZeta (squarePolynomialGaussian)

local notation "M" => fun m n => Matrix (Fin m) (Fin n) ℂ

private theorem matrixSqNorm_conjTranspose {m n : ℕ} (X : M m n) : matrixSqNorm Xᴴ = matrixSqNorm X := by
  simp only [matrixSqNorm, Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]

private theorem matrixSqNorm_unitary_left {m n : ℕ} (K : unitaryCompact ℂ m) (X : M m n) :
    matrixSqNorm (K.val.val * X) = matrixSqNorm X := by
  have hk : K.val.valᴴ = K⁻¹.val.val := by
    have hi : K⁻¹.val.val * K.val.val = 1 := congrArg Units.val (inv_mul_cancel K.val)
    calc
      _ = (K⁻¹.val.val * K.val.val) * K.val.valᴴ := by rw [hi, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, mul_conjTranspose_one K, Matrix.mul_one]
  have h := matrixGaussian_mul_unitary Xᴴ K⁻¹
  unfold matrixGaussian at h
  have he := neg_injective (Real.exp_injective (Complex.ofReal_injective h))
  rw [← matrixSqNorm_conjTranspose (K.val.val * X), Matrix.conjTranspose_mul, hk, he,
    matrixSqNorm_conjTranspose]

variable (t q : ℕ)
local notation "k" => (t + 1)
local notation "n" => (k + q + 1)
local notation "Tail" => (q + 1)
local notation "K" => unitaryCompact ℂ n
local notation "Z" => Langlands.GeneralLinear.upperUnipotent Tail ℂ
local notation "Square" => M k k
local notation "Powers" => MvPolynomial (Coordinates k k) ℂ
local notation "stack" => fun X => stackRows k Tail k X 0

private theorem matrixSqNorm_stack (X : Square) : matrixSqNorm (stack X) = matrixSqNorm X := by
  rw [matrixSqNorm, Fin.sum_univ_add (a := k) (b := Tail)]
  simp only [stackRows_left, stackRows_right, Matrix.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero, matrixSqNorm]

/-- Every real-coordinate matrix polynomial times the scale-\(2\pi\) Gaussian is realized
by a standard Schwartz matrix test. -/
theorem exists_standardMatrixTest_polynomialGaussian {m j : ℕ} (p : MvPolynomial (Coordinates m j) ℂ) :
    ∃ P : MvPolynomial (Coordinates m j) ℂ, ∀ X : M m j,
      standardMatrixTest P X = eval (coordinates X) p * (Real.exp (-(2 * Real.pi) * matrixSqNorm X) : ℂ) := by
  let u : ℂ := Real.sqrt (2 * Real.pi)
  have hu : u ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  let P := bind₁ (fun i : Coordinates m j => C u⁻¹ * X i) p
  refine ⟨P, fun A => ?_⟩
  rw [standardMatrixTest_apply]
  congr 1
  change aeval (coordinates A) (bind₁ (fun i : Coordinates m j => C u * X i) P) = aeval (coordinates A) p
  rw [aeval_bind₁]
  change aeval _ (bind₁ (fun i : Coordinates m j => C u⁻¹ * X i) p) = _
  rw [aeval_bind₁]
  congr 2
  funext i
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, ← mul_assoc,
    inv_mul_cancel₀ hu, one_mul]

/-- Each standard square polynomial Gaussian can be prescribed as the leading restriction
of a standard rectangular polynomial Gaussian at the identity retained matrix. -/
theorem exists_leadingSquareTest_one (p : Powers) :
    ∃ P : MvPolynomial (Coordinates n k) ℂ,
      ∀ X : Square, leadingSquareTest t q 1 (operatorToEntry (standardMatrixTest P)) X =
        squarePolynomialGaussian p X := by
  let i (j : Coordinates k k) : Coordinates n k := (Fin.castAdd Tail j.1, j.2)
  obtain ⟨P, hP⟩ := exists_standardMatrixTest_polynomialGaussian (rename i p)
  refine ⟨P, fun X => ?_⟩
  rw [leadingSquareTest_apply, Units.val_one, Matrix.one_mul]
  change standardMatrixTest P (stack X) = _
  rw [hP, matrixSqNorm_stack, eval_rename]
  have hC : coordinates (stack X) ∘ i = coordinates X := by
    funext j
    rcases j with ⟨a, b, c⟩
    change coordinatePartCLM c (stack X (Fin.castAdd Tail a) b) = coordinatePartCLM c (X a b)
    exact congrArg (coordinatePartCLM c) (congrFun (stackRows_left k Tail k X 0 a) b)
  rw [hC]
  rfl

private theorem coord_mul (b : Bool) (u w : ℂ) :
    coordinatePartCLM b (u * w) = coordinatePartCLM b u * (w.re : ℂ) +
      coordinatePartCLM b (Complex.I * u) * (w.im : ℂ) := by
  have he : u * w = w.re • u + w.im • (Complex.I * u) := by
    simp only [Complex.real_smul]
    calc
      _ = u * ((w.re : ℂ) + (w.im : ℂ) * Complex.I) :=
        congrArg (u * ·) (Complex.re_add_im w).symm
      _ = _ := by ring
  rw [he, map_add, map_smul, map_smul]
  simp only [Complex.real_smul]
  ring

private def coordCoefficient (j : Coordinates n k) (i : Fin k × Bool) (u : K) : ℂ :=
  coordinatePartCLM j.2.2 ((if i.2 then Complex.I else 1) * u.val.val j.1 (Fin.castAdd Tail i.1))

private theorem continuous_coordCoefficient (j : Coordinates n k) (i : Fin k × Bool) :
    Continuous (coordCoefficient t q j i) := by
  have hK : Continuous (fun u : K => (u.val.val : M n n)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact (coordinatePartCLM j.2.2).continuous.comp (continuous_const.mul
    ((continuous_apply_apply j.1 (Fin.castAdd Tail i.1 : Fin n)).comp hK))

private theorem coord_stack_mul (u : K) (X : Square) (j : Coordinates n k) :
    coordinates (u.val.val * stack X) j = ∑ i : Fin k × Bool,
      coordCoefficient t q j i u * coordinates X (i.1, j.2.1, i.2) := by
  rcases j with ⟨a, b, c⟩
  change coordinatePartCLM c ((u.val.val * stack X) a b) = _
  let g : Fin n → ℂ := fun j => u.val.val a j * stack X j b
  have hg := Fin.sum_univ_add (a := k) (b := Tail) g
  rw [Matrix.mul_apply]
  change coordinatePartCLM c (∑ j, g j) = _
  refine (congrArg (coordinatePartCLM c) hg).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [stackRows_left, stackRows_right, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, map_sum, Fintype.sum_bool, coordCoefficient, g, Bool.false_eq_true,
    ↓reduceIte, one_mul, coordinates_re, coordinates_im]
  exact Finset.sum_congr rfl fun i _ => by rw [coord_mul, add_comm]

private theorem eval_stack_mul (p : MvPolynomial (Coordinates n k) ℂ) :
    ∃ (l : ℕ) (c : Fin l → K → ℂ) (P : Fin l → Powers), (∀ j, Continuous (c j)) ∧
      ∀ u : K, ∀ X : Square,
        eval (coordinates (u.val.val * stack X)) p = ∑ j, c j u * eval (coordinates X) (P j) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨1, fun _ _ => a, fun _ => 1, fun _ => continuous_const, by simp⟩
  | add p r hp hr =>
    obtain ⟨l, c, P, hC, hP⟩ := hp
    obtain ⟨m, d, Q, hD, hQ⟩ := hr
    refine ⟨l + m, Fin.addCases c d, Fin.addCases P Q, fun j => ?_, fun u X => ?_⟩
    · exact Fin.addCases (fun j => by simpa only [Fin.addCases_left] using hC j)
        (fun j => by simpa only [Fin.addCases_right] using hD j) j
    · rw [map_add, hP, hQ, Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
  | mul_X p v hp =>
    obtain ⟨l, c, P, hC, hP⟩ := hp
    let I := Fin l × (Fin k × Bool)
    let e := Fintype.equivFin I
    let Q (i : I) := P i.1 * X (i.2.1, v.2.1, i.2.2)
    let d (i : I) (u : K) := c i.1 u * coordCoefficient t q v i.2 u
    refine ⟨Fintype.card I, fun i => d (e.symm i), fun i => Q (e.symm i),
      fun i => (hC _).mul (continuous_coordCoefficient t q v _), fun u Y => ?_⟩
    rw [map_mul, eval_X, hP, coord_stack_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    let S (i : I) := d i u * eval (coordinates Y) (Q i)
    have hs : (∑ i : Fin (Fintype.card I), S (e.symm i)) = ∑ i : I, S i :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    change _ = ∑ i, S (e.symm i)
    rw [hs, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only [S, d, Q]
    rw [map_mul, eval_X]
    ring

/-- A standard rectangular test on the chart with normalized retained determinant becomes a
finite combination of square polynomial Gaussians with one common scalar dilation.
The coefficients of the combination depend continuously on the unitary chart coordinate. -/
def ComplexGapLeadingGaussianFamilyStatement : Prop :=
  ∀ p : MvPolynomial (Coordinates n k) ℂ,
    ∃ (l : ℕ) (c : Fin l → K → ℂ) (P : Fin l → Powers), (∀ j, Continuous (c j)) ∧
      ∀ (Y : Outer k q) (z : Z) (X : Square),
        leadingSquareTest t q (retainedTail k q Y z) (operatorToEntry (standardMatrixTest p)) X =
          ∑ j, c j Y.1.2 * squarePolynomialGaussian (P j)
            ((normalizingScalar k q Y.1.1.2 : ℂ) • X)

theorem complexGapLeadingGaussianFamily : ComplexGapLeadingGaussianFamilyStatement t q := by
  intro p
  obtain ⟨l, c, P, hc, hP⟩ := eval_stack_mul t q (scalePolynomial p)
  refine ⟨l, c, P, hc, fun Y z X => ?_⟩
  let u₀ : ℂˣ := normalizingScalar k q Y.1.1.2
  have hD : (leadingScalar k q Y.1.1.2).val * X = (u₀ : ℂ) • X := by
    ext i j
    simp [u₀, leadingScalar, scalar, Matrix.scalar_apply, Matrix.diagonal_mul]
  rw [leadingSquareTest_apply, retainedTail_stack, hD]
  change standardMatrixTest p (Y.1.2.val.val * stack ((u₀ : ℂ) • X)) = _
  rw [standardMatrixTest_apply, hP, matrixSqNorm_unitary_left, matrixSqNorm_stack, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (_ * _) * _ = _ * (_ * _)
  exact mul_assoc _ _ _

end Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingCompact
