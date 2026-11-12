import Langlands.Representation.Aubert.General.DynamicIrreducibleInductionFiniteLength
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Actual dynamic irreducible finite length from supercuspidal finite length

The exact dynamic proposition of Renard VI.6.2, Lemma, follows from the
finite-length assertion of Renard VI.5.4 on the actual standard rational-point
families, taken at the enlarged carrier universe `max (u + 1) uV`. The four
structural inputs of the published standard-input reduction are now proved. -/

universe u uV

namespace Langlands.Aubert.General

/-- The finite-length assertion of Renard VI.5.4 on the actual standard
rational-point families, at carrier universe `max (u + 1) uV`, implies the exact
dynamic irreducible finite-length proposition of Renard VI.6.2 at carrier
universe `uV`. -/
def DynamicIrreducibleInductionFiniteLengthReductionStatement : Prop :=
  RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement.{u,
      max (u + 1) uV} →
    DynamicInductionIrreducibleFiniteLengthStatement.{u, uV}

/-- The reduction holds: supply the published proofs of the standard-cocharacter,
standard-Levi-intersection, relative-root-system and dynamic-quotient
compactness statements to the published standard-input reduction. -/
theorem dynamicIrreducibleInductionFiniteLengthReduction :
    DynamicIrreducibleInductionFiniteLengthReductionStatement.{u, uV} := fun hSuper =>
  dynamicInductionIrreducibleFiniteLength_of_standard_inputs hSuper
    GroupScheme.standardCocharacter GroupScheme.standardLeviIntersection
    GroupScheme.relativeRootSystem BruhatTits.dynamicParabolicQuotientCompact

end Langlands.Aubert.General
