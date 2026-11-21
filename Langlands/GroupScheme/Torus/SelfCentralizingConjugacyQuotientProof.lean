import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyQuotientReduction
import Langlands.GroupScheme.Torus.SeparatedNormalizerProof
import Langlands.GroupScheme.IdentityJetLocallyFreeProof
import Langlands.GroupScheme.IdentityJetRepresentation
import Langlands.GroupScheme.IdentityJetCentralizerComparison
import Langlands.GroupScheme.MatrixRepresentation.LocalCentralKernelReduction
import Langlands.GroupScheme.Torus.SelfCentralizingQuotientAffineOfRepresentationReduction
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingReduction
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyUniversallyClosedReduction
import Langlands.GroupScheme.Torus.RelativeTorusImageFactorizationProof
import Langlands.GroupScheme.HomScheme.SmoothAffineFiberTorusSubgroupRepresentabilityProof
import Langlands.GroupScheme.HomScheme.GeneralLinearTorusModuliAffineSumProof
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyValuationLiftProof

/-! # Affineness of the conjugacy quotient by a self-centralizing maximal torus -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

open SelfCentralizingConjugacyClosedEmbeddingReduction
open SelfCentralizingConjugacyUniversallyClosedReduction
open SelfCentralizingQuotientAffineReduction

/-- **Affineness of the conjugacy quotient** by a closed, self-centralizing,
fibrewise maximal torus of a smooth, separated, quasi-compact group with connected
affine residue fibres (SGA 3, Exposé XVI, Theorem 4.1(c)). -/
theorem selfCentralizingTorusConjugacyQuotientAffine :
    SelfCentralizingTorusConjugacyQuotientAffineStatement.{u} := by
  have rep := localCentralKernelRepresentation_of.{u} jetCentralizerStabilization_of_centerDetection
    (jetConjugationRepresentation_of identityJetLocallyFree)
  have closed := selfCentralizingConjugacyClosedEmbedding_of_universallyClosed
    (selfCentralizingConjugacyUniversallyClosed_of_valuationLift
      TorusSubgroupModuli.generalLinearAffineSum selfCentralizingConjugacyValuationLift)
  exact selfCentralizingTorusConjugacyQuotientAffine_of
    TorusSubgroupModuli.smoothAffineFiberTorusSubgroupRepresentability separatedTorusNormalizer rep
    (selfCentralizingQuotientAffineOfRepresentation_of TorusSubgroupModuli.generalLinearAffineSum
      relativeTorusImageFactorization closed)

end Langlands.GroupScheme
