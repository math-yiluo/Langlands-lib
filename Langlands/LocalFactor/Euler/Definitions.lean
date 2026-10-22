import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
The determinant Euler polynomial and its rational reciprocal. Numerical evaluation
is exposed only on the complement of the zero set of the Euler polynomial.
-/

noncomputable section

open Polynomial Module

namespace Langlands.LocalFactor

universe u v w

section Polynomial

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- The polynomial `det(1 - X A)`, expressed without selecting a basis in its API. -/
def eulerPolynomial (A : Module.End R V) : R[X] :=
  A.charpoly.reverse

/-- The definition agrees with the determinant in every finite basis. -/
theorem eulerPolynomial_eq_det (A : Module.End R V)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Basis ι R V) :
    eulerPolynomial A =
      Matrix.det (1 - (X : R[X]) • (LinearMap.toMatrix b b A).map C) := by
  rw [eulerPolynomial, ← LinearMap.charpoly_toMatrix A b, Matrix.reverse_charpoly]
  rfl

@[simp]
theorem eulerPolynomial_coeff_zero (A : Module.End R V) :
    (eulerPolynomial A).coeff 0 = 1 := by
  simp [eulerPolynomial, coeff_zero_reverse, A.charpoly_monic.leadingCoeff]

@[simp]
theorem eulerPolynomial_eval_zero (A : Module.End R V) :
    (eulerPolynomial A).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, eulerPolynomial_coeff_zero]

theorem eulerPolynomial_ne_zero [Nontrivial R] (A : Module.End R V) :
    eulerPolynomial A ≠ 0 := by
  intro h
  have := eulerPolynomial_coeff_zero A
  rw [h, coeff_zero] at this
  exact zero_ne_one this

/-- Evaluation is the intrinsic determinant of the endomorphism `1 - z A`. -/
theorem eulerPolynomial_eval (A : Module.End R V) (z : R) :
    (eulerPolynomial A).eval z = LinearMap.det (1 - z • A) := by
  classical
  let b := Module.Free.chooseBasis R V
  rw [eulerPolynomial_eq_det A b, eval_det, matPolyEquiv_eval_eq_map]
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_one]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    eval_sub, eval_mul, eval_X, eval_C]
  by_cases h : i = j <;> simp only [Matrix.one_apply, h, ite_true, ite_false,
    eval_one, eval_zero]

variable {W : Type w} [AddCommGroup W] [Module R W]
  [Module.Free R W] [Module.Finite R W]

/-- Transporting an operator across a linear equivalence does not change its Euler polynomial. -/
@[simp]
theorem eulerPolynomial_conj (e : V ≃ₗ[R] W) (A : Module.End R V) :
    eulerPolynomial (e.conj A) = eulerPolynomial A := by
  simp [eulerPolynomial]

end Polynomial

section Rational

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The reciprocal Euler polynomial as an element of the rational function field. -/
def rationalFactor (A : Module.End K V) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (eulerPolynomial A))⁻¹

theorem rationalFactor_ne_zero (A : Module.End K V) : rationalFactor A ≠ 0 := by
  exact inv_ne_zero (RatFunc.algebraMap_ne_zero (eulerPolynomial_ne_zero A))

theorem rationalFactor_mul_eulerPolynomial (A : Module.End K V) :
    rationalFactor A * algebraMap K[X] (RatFunc K) (eulerPolynomial A) = 1 :=
  inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (eulerPolynomial_ne_zero A))

/-- Points at which the reciprocal Euler polynomial has a finite value. -/
def RegularPoint (A : Module.End K V) :=
  {z : K // (eulerPolynomial A).eval z ≠ 0}

/-- The value away from poles; the codomain also records that the value is nonzero. -/
def regularFactorValue (A : Module.End K V) (z : RegularPoint A) : Kˣ :=
  (Units.mk0 ((eulerPolynomial A).eval z.1) z.2)⁻¹

@[simp]
theorem coe_regularFactorValue (A : Module.End K V) (z : RegularPoint A) :
    (regularFactorValue A z : K) = ((eulerPolynomial A).eval z.1)⁻¹ := rfl

theorem regularFactorValue_det (A : Module.End K V) (z : RegularPoint A) :
    (regularFactorValue A z : K) = (LinearMap.det (1 - z.1 • A))⁻¹ := by
  rw [coe_regularFactorValue, eulerPolynomial_eval]

/-- The constant-term normalization makes zero a regular point. -/
def zeroRegularPoint (A : Module.End K V) : RegularPoint A :=
  ⟨0, by simp⟩

@[simp]
theorem regularFactorValue_zero (A : Module.End K V) :
    regularFactorValue A (zeroRegularPoint A) = 1 := by
  apply Units.ext
  change ((eulerPolynomial A).eval 0)⁻¹ = (1 : K)
  rw [eulerPolynomial_eval_zero, inv_one]

variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

@[simp]
theorem rationalFactor_conj (e : V ≃ₗ[K] W) (A : Module.End K V) :
    rationalFactor (e.conj A) = rationalFactor A := by
  simp [rationalFactor]

end Rational

section Spectral

/-- The nonzero spectral variable `q^(-s)` for a positive real residue cardinality. -/
def spectralParameter (q : ℝ) (_hq : 0 < q) (s : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp (-s * (Real.log q : ℂ))) (Complex.exp_ne_zero _)

theorem spectralParameter_eq_cpow (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (spectralParameter q hq s : ℂ) = (q : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')]
  change Complex.exp (-s * (Real.log q : ℂ)) = _
  rw [Complex.ofReal_log hq.le, mul_comm]

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The spectral domain excludes exactly the zeros of the Euler denominator. -/
def SpectralRegularPoint (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q) :=
  {s : ℂ // (eulerPolynomial A).eval (spectralParameter q hq s : ℂ) ≠ 0}

/-- The spectral L-value on its regular domain; no value is assigned at a pole. -/
def spectralFactorValue (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint A q hq) : ℂˣ :=
  regularFactorValue A ⟨spectralParameter q hq s.1, s.2⟩

theorem spectralFactorValue_det (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint A q hq) :
    (spectralFactorValue A q hq s : ℂ) =
      (LinearMap.det (1 - (Complex.exp (-s.1 * (Real.log q : ℂ))) • A))⁻¹ := by
  exact regularFactorValue_det A ⟨spectralParameter q hq s.1, s.2⟩

end Spectral

end Langlands.LocalFactor
