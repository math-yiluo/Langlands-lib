import Langlands.Global.RankinSelberg.ComplexGapAlternateRestriction
import Langlands.Global.RankinSelberg.ComplexGodementSplitSpanning
import Langlands.Analysis.SchwartzMatrixNorm

/-! # Column factorization of the Gaussian Godement generators -/

noncomputable section

open MvPolynomial
open scoped SchwartzMap Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapGaussianFactors

open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry operatorToEntry_apply EntrySchwartz OperatorSchwartz)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinatePartCLM matrixSqNorm matrixGaussian
  gaussianPolynomial gaussianPolynomial_apply)
open ComplexGodementGaussianProduct (columnGaussianMonomial columnGaussianMonomial_apply)
open ComplexGodementGaussianProduct (gaussianPolynomial_sum_monomials)

variable (k q : ℕ)
local notation "Rows" => k + q + 1
local notation "Cols" => k + q + 2
local notation "J" => Fin (q + 2)
local notation "Rect" => Matrix (Fin Rows) (Fin Cols) ℂ
local notation "Leading" => Matrix (Fin Rows) (Fin k) ℂ

private def leadingExponents (d : Coordinates Rows Cols →₀ ℕ) : Coordinates Rows k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => d (p.1, p.2.1.castAdd (q + 2), p.2.2)

/-- A monomial Gaussian test factors over the leading rectangle and the individual tail columns. -/
def gaussianFactors (d : Coordinates Rows Cols →₀ ℕ) (c : ℂ) : GodementColumnFactors k q where
  leading := operatorToEntry (gaussianPolynomial (monomial (leadingExponents k q d) c))
  tail j := columnGaussianMonomial fun p => d (p.1, j.natAdd k, p.2)

private theorem eval_monomial_product {D : Type*} [Fintype D] (f : D → ℂ) (d : D →₀ ℕ) (c : ℂ) :
    eval f (monomial d c) = c * ∏ x, f x ^ d x := by
  rw [eval_monomial, Finsupp.prod_fintype]
  exact fun x => pow_zero (f x)

private theorem matrixSqNorm_split (X : Rect) : matrixSqNorm X =
    matrixSqNorm (fun i (j : Fin k) => X i (j.castAdd (q + 2))) + ∑ j : J, ∑ i, ‖X i (j.natAdd k)‖ ^ 2 := by
  have h (i : Fin Rows) : (∑ j : Fin Cols, ‖X i j‖ ^ 2) =
      (∑ j : Fin k, ‖X i (j.castAdd (q + 2))‖ ^ 2) + ∑ j : J, ‖X i (j.natAdd k)‖ ^ 2 :=
    Fin.sum_univ_add (a := k) (b := q + 2) _
  simp only [matrixSqNorm, h, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

private theorem matrixGaussian_split (X : Rect) : matrixGaussian X =
    matrixGaussian (fun i (j : Fin k) => X i (j.castAdd (q + 2))) *
      ∏ j : J, (Real.exp (-∑ i, ‖X i (j.natAdd k)‖ ^ 2) : ℂ) := by
  rw [matrixGaussian, matrixSqNorm_split, neg_add, Real.exp_add, Complex.ofReal_mul]
  congr 1
  have h := map_prod Complex.ofRealHom (fun j : J => Real.exp (-∑ i, ‖X i (j.natAdd k)‖ ^ 2)) Finset.univ
  change (↑(∏ j : J, Real.exp (-∑ i, ‖X i (j.natAdd k)‖ ^ 2)) : ℂ) = _ at h
  rw [← Real.exp_sum, Finset.sum_neg_distrib] at h
  exact h

private theorem exponents_split (X : Rect) (d : Coordinates Rows Cols →₀ ℕ) :
    (∏ p, coordinates X p ^ d p) =
      (∏ p : Coordinates Rows k,
        coordinates (fun i j => X i (j.castAdd (q + 2))) p ^ leadingExponents k q d p) *
      ∏ j : J, ∏ p : Fin Rows × Bool, coordinatePartCLM p.2 (X p.1 (j.natAdd k)) ^ d (p.1, j.natAdd k, p.2) := by
  simp only [Fintype.prod_prod_type, coordinates, leadingExponents]
  have h (i : Fin Rows) : (∏ j : Fin Cols, ∏ b : Bool, coordinatePartCLM b (X i j) ^ d (i,j,b)) =
      (∏ j : Fin k, ∏ b : Bool, coordinatePartCLM b (X i (j.castAdd (q + 2))) ^ d (i,j.castAdd (q + 2),b)) *
        ∏ j : J, ∏ b : Bool, coordinatePartCLM b (X i (j.natAdd k)) ^ d (i,j.natAdd k,b) :=
    Fin.prod_univ_add (a := k) (b := q + 2) _
  simp only [h, Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_comm

/-- The monomial Gaussian is exactly the evaluation of its split factors. -/
theorem gaussianPolynomial_eval_factors (d : Coordinates Rows Cols →₀ ℕ) (c : ℂ) (X : Rect) :
    operatorToEntry (gaussianPolynomial (monomial d c)) X = (gaussianFactors k q d c).eval k q X := by
  rw [operatorToEntry_apply, gaussianPolynomial_apply, eval_monomial_product, exponents_split k q,
    matrixGaussian_split k q]
  unfold GodementColumnFactors.eval gaussianFactors
  simp only [operatorToEntry_apply, gaussianPolynomial_apply, eval_monomial_product,
    columnGaussianMonomial_apply, Finset.prod_mul_distrib]
  ring

/-- Polynomial Gaussian generators are finite sums of tests split into the leading and tail factors. -/
def ComplexGapGaussianFactorsStatement : Prop :=
  ∀ p : MvPolynomial (Coordinates Rows Cols) ℂ,
    (operatorToEntry (gaussianPolynomial p) : EntrySchwartz Rows Cols) =
      ∑ d ∈ p.support, operatorToEntry (gaussianPolynomial (monomial d (p.coeff d))) ∧
    ∀ d ∈ p.support, ∀ X : Rect,
      operatorToEntry (gaussianPolynomial (monomial d (p.coeff d))) X =
        (gaussianFactors k q d (p.coeff d)).eval k q X

theorem complexGapGaussianFactors : ComplexGapGaussianFactorsStatement k q := by
  intro p
  refine ⟨?_, fun d _ => gaussianPolynomial_eval_factors k q d (p.coeff d)⟩
  ext X
  simpa only [operatorToEntry_apply, sum_apply] using
    congrArg (fun f : OperatorSchwartz Rows Cols => f X) (gaussianPolynomial_sum_monomials p)

end Langlands.Global.RankinSelbergGlobal.ComplexGapGaussianFactors
