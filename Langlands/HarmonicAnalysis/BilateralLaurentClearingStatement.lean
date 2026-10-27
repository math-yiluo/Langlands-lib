import Langlands.HarmonicAnalysis.BilateralLaurentSeries

/-!
# Clearing bilateral Laurent series from opposite support bounds

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions* (1983),
Section (4.4), printed page 408: the algebraic deduction following (4.4.1).
A series whose support is bounded below and a series whose support is bounded
above, with equal Laurent-polynomial multiples, have as common multiple the
coefficient series of a Laurent polynomial. This file states the deduction and
does not prove it.
-/

namespace Langlands.HarmonicAnalysis

/-- JPSS (4.4), after (4.4.1): if `a` has support bounded below, `b` has support
bounded above, and `P • a = Q • b` for Laurent polynomials `P` and `Q`, then this
common series is the coefficient series of a unique Laurent polynomial `R`. -/
def BilateralLaurentClearingStatement : Prop :=
  ∀ (a b : BilateralLaurentSeries) (P Q : LaurentPolynomial ℂ),
    BilateralLaurentSeries.HasLowerBoundedSupport a →
    BilateralLaurentSeries.HasUpperBoundedSupport b →
    P • a = Q • b →
    ∃! R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R = P • a ∧
      BilateralLaurentSeries.ofLaurentPolynomial R = Q • b

end Langlands.HarmonicAnalysis
