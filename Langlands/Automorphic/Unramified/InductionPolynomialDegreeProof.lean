import Langlands.Automorphic.Unramified.TraceAlgebraStatement

open scoped BigOperators
open Polynomial

namespace Langlands.Automorphic.Unramified

/-- Nonzero determinants give the full degree of the induced determinant-polynomial product. -/
theorem inductionPolynomialDegree : InductionPolynomialDegreeStatement := by
  intro a n f A hf hdet
  have hdegree (i : Fin a) : (A i).charpolyRev.natDegree = n i := by
    have hcoeff : (A i).charpoly.coeff 0 ≠ 0 := by
      intro hc
      apply hdet i
      rw [Matrix.det_eq_sign_charpoly_coeff, hc, mul_zero]
    rw [← (A i).reverse_charpoly, Polynomial.reverse_natDegree,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hcoeff), Nat.sub_zero]
    simp
  have hnonzero (i : Fin a) : (A i).charpolyRev.comp (X ^ f i) ≠ 0 := by
    intro h
    have heval := congrArg (Polynomial.eval (0 : ℂ)) h
    have hfi : f i ≠ 0 := Nat.ne_of_gt (hf i)
    simp [Polynomial.eval_comp, hfi] at heval
  rw [Polynomial.natDegree_prod _ _ (fun i _ => hnonzero i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_pow, hdegree, Nat.mul_comm]

end Langlands.Automorphic.Unramified
