import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.RationalMaximalTorusDensityProof

/-! # The closed torus envelope over an algebraic closure -/

universe u

namespace Langlands.GroupScheme

/-- The closed torus envelope over an algebraic closure, with all structural inputs discharged. -/
theorem torusGeneratedEnvelopeAlgebraicClosureInfinite : TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement.{u} :=
  torusGeneratedEnvelopeAlgebraicClosureInfinite_of.{u}
    maximalTorusBaseChange.{u} maximalTorusConjugacy.{u}
    rationalMaximalTorusConjugateDensity.{u}

end Langlands.GroupScheme
