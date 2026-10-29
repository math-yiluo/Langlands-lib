import Langlands.Analysis.LinearRecurrenceGeneratingSeriesStatement
import Langlands.Representation.RankinSelberg.RationalZeta

/-!
# Uniform Laurent rationality for eventually recurrent sequences

This closed proposition extends the natural-sequence generating-series interface
to integer-indexed sequences with a finite Laurent head and a recurrent tail,
including positive-power substitution and regular evaluation of rational functions.
It is an internal derived statement motivated by the one-variable Mellin argument;
this module supplies no proof.
-/

namespace Langlands.Analysis

/-- An eventually recurrent complex sequence vanishing below an integer cutoff
has a summable Laurent series on a punctured neighborhood of zero after every
positive-power substitution. The radius depends only on the recurrence, and
the substituted reverse characteristic polynomial clears the rational function's
denominator in the Laurent polynomial ring. The rational function is regular
and agrees with the series throughout that neighborhood. -/
def EventuallyRecurrentLaurentSeriesStatement : Prop :=
  ∀ E : LinearRecurrence ℂ,
    let Q : Polynomial ℂ :=
      1 - ∑ i : Fin E.order,
        Polynomial.C (E.coeffs i) * Polynomial.X ^ (E.order - i.val)
    Q.coeff 0 = 1 ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ m : ℕ, 0 < m →
          let D : LaurentPolynomial ℂ :=
            (Q.comp (Polynomial.X ^ m)).toLaurent
          D ≠ 0 ∧
            ∀ (c : ℤ → ℂ) (L : ℤ) (N : ℕ),
              L ≤ (N : ℤ) →
              (∀ n : ℤ, n < L → c n = 0) →
              E.IsSolution (fun j : ℕ => c ((j : ℤ) + (N : ℤ))) →
              ∃ (R : RatFunc ℂ) (P : LaurentPolynomial ℂ),
                Langlands.RankinSelberg.laurentToRatFunc P =
                    Langlands.RankinSelberg.laurentToRatFunc D * R ∧
                  ∀ z : ℂ, z ≠ 0 → ‖z ^ m‖ < ρ →
                    Summable (fun n : ℤ => c n * (z ^ m) ^ n) ∧
                      R.denom.eval z ≠ 0 ∧
                      ∑' n : ℤ, c n * (z ^ m) ^ n =
                        RatFunc.eval (RingHom.id ℂ) z R

end Langlands.Analysis
