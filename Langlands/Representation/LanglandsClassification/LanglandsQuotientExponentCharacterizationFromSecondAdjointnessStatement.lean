import Langlands.Representation.LanglandsClassification.LanglandsQuotientExponentCharacterizationStatement
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement

/-! # The exponent characterization of the Langlands quotient from second adjointness

Statement only. Renard 2026, VII.4.2, the sentence after the proof of (i) (printed p.243 /
PDF p.249), characterizes the Langlands quotient among the irreducible subquotients of
`i_P^G(σ ⊗ ψ)` by the real parts of the exponents of `r_{P̄}^G`. Its proof uses second
adjointness (Renard VI.9.6, (VI.9.6.1)), which the Library does not yet prove.

This module states that the published `LanglandsQuotientExponentCharacterizationStatement`
follows from the published `LeviSecondAdjointnessStatement` at the same universes. The
implication is neither assumed nor proved here.
-/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VII.4.2, remark after the proof of (i), for fields in universe `u` and inducing
carriers in universe `v`, holds provided second adjointness (Renard VI.9.6, (VI.9.6.1))
holds for fields in universe `u` and carriers in `max u v`. -/
def LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement : Prop :=
  LeviSecondAdjointnessStatement.{u, v} →
    LanglandsQuotientExponentCharacterizationStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
