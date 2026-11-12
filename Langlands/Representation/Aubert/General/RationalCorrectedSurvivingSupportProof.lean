import Langlands.Representation.Aubert.General.RationalCorrectedSupportAssembly
import Langlands.GroupScheme.Rational.StandardParabolicTitsRealizationOfStatements
import Langlands.GroupScheme.Rational.RelativeTitsGeometricReduction
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Proof: rational fixed-order surviving support for the corrected Aubert filtration -/

universe u

namespace Langlands.Aubert.General.RationalPointFamily

open Langlands.GroupScheme

/-- The two uniform structural prerequisites of the rational support assembly:
the standard-parabolic points statement, composed from the published relative
Tits system, generation, endpoint and order proofs, and the published
compactness of actual dynamic-parabolic quotients. -/
theorem rationalCorrectedSupportPrerequisites :
    RationalCorrectedSupportPrerequisites.{u} :=
  ⟨standardParabolicPointsStatement_of_titsRealization
      (standardParabolicTitsRealization_of_statements
        (relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization
          rationalBruhat rootRankOneFactorization)
        standardRelativeWeylGeneration)
      standardParabolicEndpoints standardParabolicOrder,
    BruhatTits.dynamicParabolicQuotientCompact⟩

/-- **Rational fixed-order surviving support.** The exact unapplied published
proposition `RationalCorrectedSurvivingSupportStatement` at field universe `u`:
both consecutive implemented corrected supports are open, the upper one is left
`P_(S \ s)`-invariant, and their difference is the single double coset
`P_(S \ s) m⁻¹ P_I`. -/
theorem rationalCorrectedSurvivingSupport :
    RationalCorrectedSurvivingSupportStatement.{u} :=
  rationalCorrectedSurvivingSupportStatement_of_prerequisites
    rationalCorrectedSupportPrerequisites

end Langlands.Aubert.General.RationalPointFamily
