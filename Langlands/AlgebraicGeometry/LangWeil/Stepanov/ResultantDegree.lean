import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Column-degree bound for the Sylvester resultant over `R[X]`

The resultant of two polynomials with coefficients in `R[X]` is a polynomial in the inner
variable. Its degree is bounded by the Sylvester column counts times the coefficient degrees.
This is the form of the bound used in the Stepanov–Schmidt argument.
-/

open Polynomial

universe u

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

/-- **Determinant bound.** If every entry in column `b` of a square matrix over `R[X]` has degree
at most `c b`, then its determinant has degree at most `∑ b, c b`. -/
theorem natDegree_det_le_sum_of_col {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u}
    [CommRing R] (M : Matrix ι ι R[X]) (c : ι → ℕ) (h : ∀ a b, (M a b).natDegree ≤ c b) :
    M.det.natDegree ≤ ∑ b, c b := by
  rw [Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun τ _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  exact le_trans (natDegree_prod_le (s := Finset.univ) (f := fun b => M (τ b) b))
    (Finset.sum_le_sum fun b _ => h _ _)

/-- If every coefficient of `p` has degree at most `mp` and every coefficient of `r` has degree
at most `mr`, then `Res(p, r)` computed with the Sylvester sizes `a` and `b` has degree at most
`b * mp + a * mr`. Mathlib's `sylvester p r a b` has `a` columns of coefficients of `r` followed
by `b` columns of coefficients of `p`. -/
theorem resultant_natDegree_le {R : Type u} [CommRing R] (p r : Polynomial (Polynomial R))
    (a b mp mr : ℕ) (hp : ∀ i, (p.coeff i).natDegree ≤ mp)
    (hr : ∀ i, (r.coeff i).natDegree ≤ mr) :
    (Polynomial.resultant p r a b).natDegree ≤ b * mp + a * mr := by
  classical
  have key := natDegree_det_le_sum_of_col (sylvester p r a b)
    (Fin.addCases (fun _ => mr) (fun _ => mp)) ?_
  · rw [resultant]
    refine key.trans (le_of_eq ?_)
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  · intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hr _
      · rw [natDegree_zero]; exact Nat.zero_le _
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hp _
      · rw [natDegree_zero]; exact Nat.zero_le _

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
