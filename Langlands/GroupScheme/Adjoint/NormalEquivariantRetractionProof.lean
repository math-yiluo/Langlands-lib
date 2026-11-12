import Langlands.GroupScheme.Adjoint.NormalEquivariantRetractionReduction
import Langlands.GroupScheme.Reductive.SemisimpleNormalComplementConstruction
import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Equivariant retractions onto normal adjoint subgroups: proof -/

universe u

namespace Langlands.GroupScheme

/-- A normal closed adjoint subgroup of an adjoint group over an algebraically
closed field admits an actual group-scheme retraction, equivariant on every
test scheme for compatible actions of a split torus. -/
theorem normalAdjointEquivariantRetraction :
    NormalAdjointEquivariantRetractionStatement.{u} :=
  normalAdjointEquivariantRetraction_of_semisimpleNormalComplement
    (semisimpleNormalComplement_of_almostSimpleGeneration
      (semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter
        (semisimpleRootGenerationReduction rootRankOneFactorization
          (algClosedMaximalTorusCentralizer_fromQuotient
            dynamicCentralizerReductive solvableTorusQuotient))
        absoluteRootVectorLine maximalTorusConjugacy))

end Langlands.GroupScheme
