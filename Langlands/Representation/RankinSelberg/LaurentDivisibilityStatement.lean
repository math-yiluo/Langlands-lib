import Langlands.Representation.RankinSelberg.RationalZeta

/-!
# Laurent-span criteria for polynomial divisibility

Internal algebraic statements about the Laurent scalar action through
`laurentToRatFunc`. This module defines propositions only.
-/

open Polynomial

namespace Langlands.RankinSelberg

/-- Membership of a reciprocal in a Laurent span is equivalent to polynomial
multiplicity after clearing a nonnegative power of `X`. -/
def ReciprocalLaurentSpanClearingStatement : Prop :=
  ∀ (P A : ℂ[X]), P ≠ 0 → A ≠ 0 →
    ((algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈
        Submodule.span LaurentCoefficients
          {(algebraMap ℂ[X] RationalFunctions A)⁻¹} ↔
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * A = Q * P)

/-- Constant coefficient one removes the power of `X` from the divisibility
criterion for reciprocal Laurent-span membership. -/
def NormalizedReciprocalLaurentSpanDivisibilityStatement : Prop :=
  ∀ (P A : ℂ[X]), P.coeff 0 = 1 → A ≠ 0 →
    ((algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈
        Submodule.span LaurentCoefficients
          {(algebraMap ℂ[X] RationalFunctions A)⁻¹} ↔
      P ∣ A)

/-- Inclusion of Laurent spans with normalized reciprocal generators is
polynomial divisibility in the displayed direction. -/
def NormalizedGeneratorSpanDivisibilityStatement : Prop :=
  ∀ (S T : Set RationalFunctions) (P A : ℂ[X]),
    IsNormalizedGenerator S P → IsNormalizedGenerator T A →
      (zetaSpan S ≤ zetaSpan T ↔ P ∣ A)

/-- The three Laurent-span criteria for polynomial divisibility, stated together. -/
def LaurentPolynomialDivisibilityStatement : Prop :=
  ReciprocalLaurentSpanClearingStatement ∧
    NormalizedReciprocalLaurentSpanDivisibilityStatement ∧
    NormalizedGeneratorSpanDivisibilityStatement

end Langlands.RankinSelberg
