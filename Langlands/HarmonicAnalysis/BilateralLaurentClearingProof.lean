import Langlands.HarmonicAnalysis.BilateralLaurentClearingStatement

/-!
# Proof of bilateral Laurent clearing from opposite support bounds

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions* (1983),
Section (4.4), printed page 408: the algebraic deduction following (4.4.1).
A Laurent-polynomial multiple of a series keeps a one-sided support bound, since
the action is a finite convolution. If `P • a = Q • b` with the support of `a`
bounded below and that of `b` bounded above, the common series has support
bounded on both sides, hence finite, so it is the coefficient series of a
Laurent polynomial. That polynomial is unique because the coefficient embedding
is injective.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis

namespace BilateralLaurentSeries

/-- A Laurent-polynomial multiple of a series whose support is bounded below again
has support bounded below. -/
theorem HasLowerBoundedSupport.laurent_smul {a : BilateralLaurentSeries}
    (ha : HasLowerBoundedSupport a) (P : LaurentPolynomial ℂ) :
    HasLowerBoundedSupport (P • a) := by
  obtain ⟨N, hN⟩ := (hasLowerBoundedSupport_iff a).1 ha
  obtain ⟨m, hm⟩ := P.coeff.support.bddBelow
  refine (hasLowerBoundedSupport_iff _).2 ⟨N + m, fun n hn => ?_⟩
  rw [laurent_smul_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hmk : m ≤ k := hm (Finset.mem_coe.2 hk)
  rw [hN (n - k) (by omega), mul_zero]

/-- A Laurent-polynomial multiple of a series whose support is bounded above again
has support bounded above. -/
theorem HasUpperBoundedSupport.laurent_smul {b : BilateralLaurentSeries}
    (hb : HasUpperBoundedSupport b) (P : LaurentPolynomial ℂ) :
    HasUpperBoundedSupport (P • b) := by
  obtain ⟨N, hN⟩ := (hasUpperBoundedSupport_iff b).1 hb
  obtain ⟨M, hM⟩ := P.coeff.support.bddAbove
  refine (hasUpperBoundedSupport_iff _).2 ⟨N + M, fun n hn => ?_⟩
  rw [laurent_smul_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkM : k ≤ M := hM (Finset.mem_coe.2 hk)
  rw [hN (n - k) (by omega), mul_zero]

/-- A series whose support is bounded both below and above has finite support. -/
theorem finite_support_of_hasLowerBoundedSupport_of_hasUpperBoundedSupport
    {c : BilateralLaurentSeries} (hlo : HasLowerBoundedSupport c)
    (hhi : HasUpperBoundedSupport c) : {n : ℤ | c n ≠ 0}.Finite :=
  BddBelow.finite_of_bddAbove hlo hhi

/-- A series whose support is bounded both below and above is the coefficient
series of a Laurent polynomial. -/
theorem exists_ofLaurentPolynomial_eq_of_hasLowerBoundedSupport_of_hasUpperBoundedSupport
    {c : BilateralLaurentSeries} (hlo : HasLowerBoundedSupport c)
    (hhi : HasUpperBoundedSupport c) :
    ∃ R : LaurentPolynomial ℂ, ofLaurentPolynomial R = c := by
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun n : ℤ => c n)
    (finite_support_of_hasLowerBoundedSupport_of_hasUpperBoundedSupport hlo hhi)), ?_⟩
  ext n
  rw [ofLaurentPolynomial_apply, AddMonoidAlgebra.coeff_ofCoeff]
  rfl

end BilateralLaurentSeries

open BilateralLaurentSeries in
/-- JPSS (4.4), after (4.4.1): if `a` has support bounded below, `b` has support
bounded above, and `P • a = Q • b`, then this common series is the coefficient
series of a unique Laurent polynomial. -/
theorem bilateralLaurentClearing : BilateralLaurentClearingStatement := by
  intro a b P Q ha hb hab
  have hlo : HasLowerBoundedSupport (P • a) := ha.laurent_smul P
  have hhi : HasUpperBoundedSupport (P • a) := hab ▸ hb.laurent_smul Q
  obtain ⟨R, hR⟩ :=
    exists_ofLaurentPolynomial_eq_of_hasLowerBoundedSupport_of_hasUpperBoundedSupport hlo hhi
  exact ⟨R, ⟨hR, hR.trans hab⟩,
    fun S hS => ofLaurentPolynomial_injective (hS.1.trans hR.symm)⟩

end Langlands.HarmonicAnalysis
