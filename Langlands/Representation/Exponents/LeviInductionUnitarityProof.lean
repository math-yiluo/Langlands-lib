import Langlands.Representation.Exponents.MaximalLeviReducibilityInductionInputs
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # Admissibility and unitarity of normalized induction from actual rational parabolics

Renard III.2.3 and IV.2.3 for an actual rational parabolic `P = MN` of a connected
reductive group over a nonarchimedean local field: normalized induction
`leviInductionFunctor` sends admissible representations of `M(F)` to admissible
representations of `G(F)`, and unitarizable ones to unitarizable ones.

The published reductions `leviInductionAdmissible_of_quotientCompact` and
`leviInductionUnitarizable_of_inputs` derive these statements from compactness of the
parabolic quotient, unimodularity of rational points of connected reductive groups,
standard cocharacters and existence of parabolic root presentations. All four inputs
now have published proofs, which this module applies.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- **Renard III.2.3** for actual rational parabolics: normalized induction preserves
admissibility. -/
theorem leviInductionAdmissible : LeviInductionAdmissibleStatement.{u, v} :=
  leviInductionAdmissible_of_quotientCompact arbitraryParabolicQuotientCompact

/-- **Renard IV.2.3** for actual rational parabolics: normalized induction preserves
unitarizability. -/
theorem leviInductionUnitarizable : LeviInductionUnitarizableStatement.{u, v} :=
  leviInductionUnitarizable_of_inputs RationalPointFamily.rationalReductiveUnimodularity
    standardCocharacter arbitraryParabolicQuotientCompact parabolicRootPresentationExistence

end Langlands.Aubert.General.RepresentedParabolic
