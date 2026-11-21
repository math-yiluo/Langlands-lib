import Langlands.Global.RankinSelberg.ComplexGodementSplitSpanning
import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial
import Langlands.Representation.Archimedean.ComplexReverseTwist

/-! # Column products of Gaussian-polynomial tests -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator SchwartzMap
open MvPolynomial

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial

open Langlands.Archimedean
open ComplexGodementColumnProduct (columnProduct columnProduct_apply lastColumn leadingColumns)

private abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

variable {m n : ℕ}

/-- View a vector as a matrix with one column, with inverse given by evaluation in that column. -/
private def columnMatrix (m : ℕ) : (Fin m → ℂ) ≃L[ℝ] Mat m 1 :=
  ({ toFun v := Matrix.of fun i _ => v i
     invFun A i := A i 0
     left_inv v := rfl
     right_inv A := by
       ext i j
       have hj : j = 0 := Subsingleton.elim _ _
       subst j
       rfl
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : (Fin m → ℂ) ≃ₗ[ℝ] Mat m 1).toContinuousLinearEquiv

private theorem columnMatrix_apply (v : Fin m → ℂ) (i : Fin m) (j : Fin 1) :
    columnMatrix m v i j = v i := rfl

/-- A Gaussian polynomial on a single complex column, as a vector Schwartz test. -/
def columnGaussianPolynomial (q : MvPolynomial (Coordinates m 1) ℂ) : 𝓢(Fin m → ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (columnMatrix m) (gaussianPolynomial q)

private theorem columnGaussianPolynomial_apply (q : MvPolynomial (Coordinates m 1) ℂ)
    (v : Fin m → ℂ) :
    columnGaussianPolynomial q v = gaussianPolynomial q (columnMatrix m v) := rfl

private theorem matrixGaussian_column_split (A : Mat m (m + 1)) :
    matrixGaussian A =
      matrixGaussian (leadingColumns A) * matrixGaussian (columnMatrix m (lastColumn A)) := by
  have hnorm : matrixSqNorm A =
      matrixSqNorm (leadingColumns A) + matrixSqNorm (columnMatrix m (lastColumn A)) := by
    calc
      matrixSqNorm A =
          ∑ i : Fin m, ((∑ j : Fin m, ‖A i j.castSucc‖ ^ 2) + ‖A i (Fin.last m)‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => Fin.sum_univ_castSucc (fun j => ‖A i j‖ ^ 2)
      _ = _ := by simp only [matrixSqNorm, leadingColumns, Matrix.submatrix_apply, id_eq,
        Fin.sum_univ_one, columnMatrix_apply, lastColumn, Finset.sum_add_distrib]
  simp only [matrixGaussian, hnorm, neg_add, Real.exp_add, Complex.ofReal_mul]

private theorem exists_eval_column_split (p : MvPolynomial (Coordinates m (m + 1)) ℂ) :
    ∃ (l : ℕ) (P : Fin l → MvPolynomial (Coordinates m m) ℂ)
      (Q : Fin l → MvPolynomial (Coordinates m 1) ℂ),
      ∀ A : Mat m (m + 1), eval (coordinates A) p =
        ∑ j, eval (coordinates (leadingColumns A)) (P j) *
          eval (coordinates (columnMatrix m (lastColumn A))) (Q j) := by
  induction p using MvPolynomial.induction_on with
  | C z =>
      exact ⟨1, fun _ => C z, fun _ => 1, by simp⟩
  | add p q hp hq =>
      obtain ⟨l, P, Q, hp⟩ := hp
      obtain ⟨l', P', Q', hq⟩ := hq
      refine ⟨l + l', Fin.addCases P P', Fin.addCases Q Q', fun A => ?_⟩
      rw [map_add, hp, hq, Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
  | mul_X p v hp =>
      obtain ⟨l, P, Q, hp⟩ := hp
      rcases v with ⟨i, j, b⟩
      refine Fin.lastCases ?_ (fun j => ?_) j
      · refine ⟨l, P, fun k => Q k * X (i, 0, b), fun A => ?_⟩
        rw [map_mul, eval_X, hp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [map_mul, eval_X, mul_assoc]
        rfl
      · refine ⟨l, fun k => P k * X (i, j, b), Q, fun A => ?_⟩
        rw [map_mul, eval_X, hp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [map_mul, eval_X, mul_assoc]
        congr 1
        exact mul_comm _ _

/-- A rectangular Gaussian polynomial is a finite sum of column products. Each square
Gaussian-polynomial factor has finite-dimensional inverse left unitary translate span. -/
def ComplexGodementGaussianColumnSplitStatement : Prop :=
  ∀ (m : ℕ) (p : MvPolynomial (Coordinates m (m + 1)) ℂ),
    ∃ (l : ℕ) (P : Fin l → MvPolynomial (Coordinates m m) ℂ)
      (Q : Fin l → MvPolynomial (Coordinates m 1) ℂ),
      gaussianPolynomial p = ∑ j, columnProduct (gaussianPolynomial (P j)) (columnGaussianPolynomial (Q j)) ∧
      ∀ j, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ m =>
        fun A : Mat m m => gaussianPolynomial (P j) (k.val⁻¹.val * A)))

theorem complexGodementGaussianColumnSplit : ComplexGodementGaussianColumnSplitStatement := by
  intro m p
  obtain ⟨l, P, Q, hp⟩ := exists_eval_column_split p
  refine ⟨l, P, Q, ?_, fun j => ComplexGodementGaussianProduct.finiteDimensional_gaussianPolynomial_left (P j)⟩
  ext A
  simp only [sum_apply, columnProduct_apply, columnGaussianPolynomial_apply, gaussianPolynomial_apply,
    hp, matrixGaussian_column_split, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_mul_mul_comm _ _ _ _

end Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial
