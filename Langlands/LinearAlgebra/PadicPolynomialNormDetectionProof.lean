import Langlands.LinearAlgebra.PadicPolynomialNormDetectionStatement
import Langlands.Algebra.DegreeDeterminant.DetComparison

/-! # Detecting a p-adic polynomial by norms of resultants -/

noncomputable section

open Polynomial

namespace Langlands.LinearAlgebra.PadicNormDetection

open Langlands.Algebra.DegreeDeterminant

section Resultant

variable {K : Type*} [Field K]

/-- A monic first argument makes the resultant independent of a larger bound
on the degree of its second argument. -/
theorem resultant_monic_degree (P F : K[X]) (hP : P.Monic) (N : ℕ)
    (hF : F.natDegree ≤ N) :
    resultant P F P.natDegree N = resultant P F := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree,
    hP.leadingCoeff, one_pow, one_mul]

/-- The resultant as a polynomial in a bounded coefficient vector. -/
def coefficientResultant (P : K[X]) (n : ℕ) : MvPolynomial (Fin (n + 1)) K :=
  resultant (P.map MvPolynomial.C) (ofCoeffs fun i => MvPolynomial.X i)
    P.natDegree n

theorem eval_coefficientResultant (P : K[X]) (n : ℕ) (x : Fin (n + 1) → K) :
    MvPolynomial.eval x (coefficientResultant P n) =
      resultant P (ofCoeffs x) P.natDegree n := by
  rw [coefficientResultant, ← resultant_map_map, Polynomial.map_map, map_ofCoeffs]
  congr 2
  · ext i
    simp
  · simp

/-- The resultant of `P` with `F + t`, as a polynomial in `t`. -/
def resultantLine (P F : K[X]) : K[X] :=
  resultant (P.map C) (F.map C + C X) P.natDegree F.natDegree

theorem eval_resultantLine (P F : K[X]) (hP : P.Monic) (t : K) :
    (resultantLine P F).eval t = resultant P (F + C t) := by
  change (evalRingHom t) (resultantLine P F) = _
  rw [resultantLine, ← resultant_map_map, Polynomial.map_add, Polynomial.map_map,
    Polynomial.map_map, Polynomial.map_C]
  have hcomp : (evalRingHom t).comp C = RingHom.id K := by
    ext c
    simp
  rw [hcomp, Polynomial.map_id, Polynomial.map_id]
  change resultant P (F + C (X.eval t)) P.natDegree F.natDegree = _
  rw [eval_X]
  apply resultant_monic_degree _ _ hP
  exact (natDegree_add_le _ _).trans (by simp)

variable {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]

theorem map_resultant_eq_prod (P F : K[X]) (hP : P.Monic) :
    algebraMap K L (resultant P F) =
      ((P.map (algebraMap K L)).roots.map fun q =>
        (F.map (algebraMap K L)).eval q).prod := by
  rw [← resultant_map_map, ← natDegree_map (p := P) (algebraMap K L),
    resultant_eq_prod_eval _ _ _ natDegree_map_le
    (IsAlgClosed.splits _), (hP.map _).leadingCoeff, one_pow, one_mul]

theorem map_resultantLine [Infinite K] (P F : K[X]) (hP : P.Monic) :
    (resultantLine P F).map (algebraMap K L) =
      ((P.map (algebraMap K L)).roots.map fun q =>
        X + C ((F.map (algebraMap K L)).eval q)).prod := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective (algebraMap K L).injective).mono ?_
  rintro _ ⟨t, rfl⟩
  simp only [Set.mem_ofPred_eq]
  rw [eval_map_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval,
    eval_resultantLine P F hP, map_resultant_eq_prod _ _ hP, eval_multiset_prod,
    Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro q _
  simp [add_comm]

theorem resultantLine_ne_zero [Infinite K] (P F : K[X]) (hP : P.Monic) :
    resultantLine P F ≠ 0 := by
  intro hzero
  have hmon : (((P.map (algebraMap K (AlgebraicClosure K))).roots.map fun q =>
      X + C ((F.map (algebraMap K (AlgebraicClosure K))).eval q)).prod).Monic := by
    apply monic_multiset_prod_of_monic
    intro q _
    exact monic_X_add_C _
  rw [← map_resultantLine P F hP, hzero, Polynomial.map_zero] at hmon
  exact hmon.ne_zero rfl

/-- The order of the resultant line at zero counts roots of `P` where the
unscaled test polynomial vanishes. -/
theorem rootMultiplicity_resultantLine [Infinite K] (P π : K[X]) (hP : P.Monic)
    (c : K) (hc : c ≠ 0) :
    rootMultiplicity 0 (resultantLine P (C c * π)) = rootCount L P π := by
  classical
  rw [eq_rootMultiplicity_map (algebraMap K L).injective, map_zero,
    map_resultantLine P _ hP, rootMultiplicity_zero_prod, rootCount]
  congr 1
  apply Multiset.filter_congr
  intro q _
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, mul_eq_zero,
    eval_map_algebraMap]
  have : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  simp [this]

end Resultant

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- Integer coefficient tests extend by continuity to integral p-adic
coefficient vectors, wherever the second resultant is nonzero. -/
theorem norm_resultant_eq_of_integral_coeffs (P Q F : ℚ_[p][X])
    (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ G : ℤ[X],
      ‖resultant P (G.map (Int.castRingHom ℚ_[p]))‖ =
        ‖resultant Q (G.map (Int.castRingHom ℚ_[p]))‖)
    (hF : ∀ i, ‖F.coeff i‖ ≤ 1) (hQF : resultant Q F ≠ 0) :
    ‖resultant P F‖ = ‖resultant Q F‖ := by
  let n := F.natDegree
  have heval : ∀ (R : ℚ_[p][X]) (hR : R.Monic) (x : Fin (n + 1) → ℚ_[p]),
      MvPolynomial.eval x (coefficientResultant R n) = resultant R (ofCoeffs x) := by
    intro R hR x
    rw [eval_coefficientResultant, resultant_monic_degree _ _ hR]
    have := natDegree_ofCoeffs_lt x (by omega)
    omega
  have hcoeff : ofCoeffs (fun i : Fin (n + 1) => F.coeff i) = F :=
    ofCoeffs_coeff F (by dsimp [n]; omega)
  have key := norm_eval_eq_of_natCast (coefficientResultant P n)
    (coefficientResultant Q n) ?_ (fun i => F.coeff i) (fun i => hF i) ?_
  · rw [heval P hP, heval Q hQ, hcoeff] at key
    exact key
  · intro x _
    rw [heval P hP, heval Q hQ]
    have hx : (ofCoeffs (fun i : Fin (n + 1) => (x i : ℤ))).map
        (Int.castRingHom ℚ_[p]) = ofCoeffs (fun i => (x i : ℚ_[p])) := by
      rw [map_ofCoeffs]
      simp
    rw [← hx]
    exact h _
  · rw [heval Q hQ, hcoeff]
    exact hQF

end Padic

end Langlands.LinearAlgebra.PadicNormDetection

namespace Langlands.LinearAlgebra

open Langlands.Algebra.DegreeDeterminant PadicNormDetection

/-- Monic p-adic polynomials of equal degree are determined by the norms of
their resultants against all integer polynomials. -/
theorem padicPolynomialNormDetection : PadicPolynomialNormDetectionStatement := by
  intro p _ P Q hP hQ hdeg htests
  let L := AlgebraicClosure ℚ_[p]
  apply eq_of_rootCount_eq L P.natDegree P.natDegree P Q rfl hP hQ le_rfl
    (le_of_eq hdeg.symm)
  intro π _ _ _
  obtain ⟨c, hc0, hcint⟩ := exists_integral_multiple π
  rw [← rootMultiplicity_resultantLine (L := L) P π hP c hc0,
    ← rootMultiplicity_resultantLine (L := L) Q π hQ c hc0]
  apply rootMultiplicity_zero_eq_of_norm_eval_eq _ _ (resultantLine_ne_zero Q _ hQ)
  intro t ht hQt
  rw [eval_resultantLine _ _ hP, eval_resultantLine _ _ hQ] at *
  apply norm_resultant_eq_of_integral_coeffs _ _ _ hP hQ htests ?_ hQt
  intro i
  rw [coeff_add, coeff_C]
  refine (Padic.nonarchimedean _ _).trans (max_le (hcint i) ?_)
  split_ifs
  · exact ht
  · simp

end Langlands.LinearAlgebra
