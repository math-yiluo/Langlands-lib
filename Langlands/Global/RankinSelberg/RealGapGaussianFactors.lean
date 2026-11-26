import Langlands.Global.RankinSelberg.RealGapAlternateRestriction
import Langlands.Global.RankinSelberg.RealAdjacentGaussianSplit

/-! # Column factorization of the real square Gaussian tests -/

noncomputable section

open MvPolynomial
open scoped SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapGaussianFactors

open RealGapAlternateRestriction (GodementColumnFactors)
open RealGodementGaussianPolynomial (Coordinates coordinates matrixSqNorm matrixGaussian
  gaussianPolynomial gaussianPolynomial_apply)
open RealJacquet (columnGaussianMonomial columnGaussianMonomial_apply gaussianPolynomial_sum_monomials)

variable (k q : ℕ)
local notation "Rows" => k + q + 1
local notation "Sq" => Matrix (Fin Rows) (Fin Rows) ℝ

private def leadingExponents (d : Coordinates Rows Rows →₀ ℕ) : Coordinates Rows k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => d (v.1, v.2.castAdd (q + 1))

/-- A square monomial Gaussian test factors over the leading rectangle and the individual tail
columns; the free last column of the rectangle carries an arbitrary test `f`. -/
def gaussianFactors (d : Coordinates Rows Rows →₀ ℕ) (c : ℂ) (f : 𝓢(Fin Rows → ℝ, ℂ)) :
    GodementColumnFactors k q where
  leading := gaussianPolynomial (monomial (leadingExponents k q d) c)
  tail := Fin.lastCases f fun j : Fin (q + 1) =>
    columnGaussianMonomial (r := k + q) fun i => d (i, j.natAdd k)

private theorem eval_monomial_product {D : Type*} [Fintype D] (g : D → ℂ) (d : D →₀ ℕ) (c : ℂ) :
    eval g (monomial d c) = c * ∏ x, g x ^ d x := by
  rw [eval_monomial, Finsupp.prod_fintype]
  exact fun x => pow_zero (g x)

private theorem matrixSqNorm_split (A : Sq) : matrixSqNorm A =
    matrixSqNorm (fun i (j : Fin k) => A i (j.castAdd (q + 1))) +
      ∑ j : Fin (q + 1), ∑ i, A i (j.natAdd k) ^ 2 := by
  have h (i : Fin Rows) : (∑ j : Fin Rows, A i j ^ 2) =
      (∑ j : Fin k, A i (j.castAdd (q + 1)) ^ 2) + ∑ j : Fin (q + 1), A i (j.natAdd k) ^ 2 :=
    Fin.sum_univ_add (a := k) (b := q + 1) _
  simp only [matrixSqNorm, h, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

private theorem matrixGaussian_split (A : Sq) : matrixGaussian A =
    matrixGaussian (fun i (j : Fin k) => A i (j.castAdd (q + 1))) *
      ∏ j : Fin (q + 1), (Real.exp (-∑ i, A i (j.natAdd k) ^ 2) : ℂ) := by
  rw [matrixGaussian, matrixSqNorm_split, neg_add, Real.exp_add, Complex.ofReal_mul]
  congr 1
  have h := map_prod Complex.ofRealHom (fun j : Fin (q + 1) => Real.exp (-∑ i, A i (j.natAdd k) ^ 2))
    Finset.univ
  change (↑(∏ j : Fin (q + 1), Real.exp (-∑ i, A i (j.natAdd k) ^ 2)) : ℂ) = _ at h
  rw [← Real.exp_sum, Finset.sum_neg_distrib] at h
  exact h

private theorem exponents_split (A : Sq) (d : Coordinates Rows Rows →₀ ℕ) :
    (∏ v, coordinates A v ^ d v) =
      (∏ v : Coordinates Rows k,
        coordinates (fun i j => A i (j.castAdd (q + 1))) v ^ leadingExponents k q d v) *
      ∏ j : Fin (q + 1), ∏ i : Fin Rows, (A i (j.natAdd k) : ℂ) ^ d (i, j.natAdd k) := by
  simp only [Fintype.prod_prod_type, coordinates, leadingExponents]
  have h (i : Fin Rows) : (∏ j : Fin Rows, (A i j : ℂ) ^ d (i, j)) =
      (∏ j : Fin k, (A i (j.castAdd (q + 1)) : ℂ) ^ d (i, j.castAdd (q + 1))) *
        ∏ j : Fin (q + 1), (A i (j.natAdd k) : ℂ) ^ d (i, j.natAdd k) :=
    Fin.prod_univ_add (a := k) (b := q + 1) _
  simp only [h, Finset.prod_mul_distrib, Finsupp.coe_equivFunOnFinite_symm]
  congr 1
  exact Finset.prod_comm

/-- The square monomial Gaussian is exactly the square evaluation of its split factors. -/
theorem gaussianPolynomial_eval_factors (d : Coordinates Rows Rows →₀ ℕ) (c : ℂ)
    (f : 𝓢(Fin Rows → ℝ, ℂ)) (A : Sq) :
    gaussianPolynomial (monomial d c) A = (gaussianFactors k q d c f).squareEval k q A := by
  rw [gaussianPolynomial_apply, eval_monomial_product, exponents_split k q, matrixGaussian_split k q]
  unfold GodementColumnFactors.squareEval gaussianFactors
  simp only [gaussianPolynomial_apply, eval_monomial_product, Fin.lastCases_castSucc,
    columnGaussianMonomial_apply, Finset.prod_mul_distrib]
  ring

/-- Square polynomial Gaussian tests are finite sums of tests split into leading and tail factors. -/
def RealGapGaussianFactorsStatement : Prop :=
  ∀ p : MvPolynomial (Coordinates Rows Rows) ℂ,
    gaussianPolynomial p = ∑ d ∈ p.support, gaussianPolynomial (monomial d (p.coeff d)) ∧
    ∀ d ∈ p.support, ∀ (f : 𝓢(Fin Rows → ℝ, ℂ)) (A : Sq),
      gaussianPolynomial (monomial d (p.coeff d)) A =
        (gaussianFactors k q d (p.coeff d) f).squareEval k q A

theorem realGapGaussianFactors : RealGapGaussianFactorsStatement k q :=
  fun p => ⟨gaussianPolynomial_sum_monomials p,
    fun d _ f A => gaussianPolynomial_eval_factors k q d (p.coeff d) f A⟩

end Langlands.Global.RankinSelbergGlobal.RealGapGaussianFactors
