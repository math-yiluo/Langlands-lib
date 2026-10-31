import Langlands.Representation.Unramified.HeckeOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Scalar multiplication of the existing unordered spectra -/

noncomputable section
universe uF
open scoped BigOperators
open Polynomial

namespace Langlands.Unramified

namespace Eigenvalues

variable {n m : ℕ}

/-- Multiply each nonzero eigenvalue by the same nonzero complex number. -/
def scale (a : ℂˣ) (s : Eigenvalues n) : Eigenvalues n :=
  s.map (fun z => a * z)

@[simp]
theorem scale_ofTuple (a : ℂˣ) (z : Fin n → ℂˣ) :
    scale a (ofTuple z) = ofTuple (fun i => a * z i) := by
  apply Sym.ext
  simp [scale, ofTuple, List.map_ofFn, Function.comp_def]

@[simp]
theorem scale_one (s : Eigenvalues n) : scale 1 s = s := by
  simp [scale]

theorem scale_scale (a b : ℂˣ) (s : Eigenvalues n) :
    scale a (scale b s) = scale (a * b) s := by
  simp [scale, Sym.map_map, mul_assoc]

theorem scale_directSum (a : ℂˣ) (s : Eigenvalues n) (t : Eigenvalues m) :
    scale a (directSum s t) = directSum (scale a s) (scale a t) := by
  apply Sym.ext
  simp [scale, directSum, Sym.coe_map, Sym.coe_append]

theorem power_scale (a : ℂˣ) (s : Eigenvalues n) (k : ℕ) :
    power (scale a s) k = scale (a ^ k) (power s k) := by
  simp [scale, power, Sym.map_map, mul_pow]

theorem powerTrace_scale (a : ℂˣ) (s : Eigenvalues n) (k : ℕ) :
    powerTrace (scale a s) k = (a : ℂ) ^ k * powerTrace s k := by
  obtain ⟨z, rfl⟩ := ofTuple_surjective n s
  simp only [scale_ofTuple, powerTrace_ofTuple, Units.val_mul, mul_pow,
    Finset.mul_sum]

/-- Scaling the roots amounts to scaling the variable of the Euler denominator. -/
theorem eulerPolynomial_scale (a : ℂˣ) (s : Eigenvalues n) :
    eulerPolynomial (scale a s) = (eulerPolynomial s).comp (C (a : ℂ) * X) := by
  obtain ⟨z, rfl⟩ := ofTuple_surjective n s
  rw [scale_ofTuple, eulerPolynomial_ofTuple, eulerPolynomial_ofTuple, Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Units.val_mul, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, map_mul]
  ring

theorem eulerPolynomial_scale_coeff (a : ℂˣ) (s : Eigenvalues n) (i : ℕ) :
    (eulerPolynomial (scale a s)).coeff i =
      (a : ℂ) ^ i * (eulerPolynomial s).coeff i := by
  rw [eulerPolynomial_scale, Polynomial.comp_C_mul_X_coeff, mul_comm]

end Eigenvalues

theorem elementaryCoefficient_scale {n : ℕ} (a : ℂˣ) (s : Eigenvalues n) (i : ℕ) :
    elementaryCoefficient (Eigenvalues.scale a s) i =
      (a : ℂ) ^ i * elementaryCoefficient s i := by
  rw [elementaryCoefficient, Eigenvalues.eulerPolynomial_scale_coeff, elementaryCoefficient]
  ring

theorem standardHeckeScalar_scale
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
    (a : ℂˣ) (s : Eigenvalues (r + 1)) (i : Fin (r + 2)) :
    standardHeckeScalar F (Eigenvalues.scale a s) i =
      (a : ℂ) ^ i.val * standardHeckeScalar F s i := by
  rw [standardHeckeScalar, elementaryCoefficient_scale, standardHeckeScalar]
  ring

end Langlands.Unramified
