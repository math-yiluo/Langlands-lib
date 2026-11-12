import Langlands.GroupScheme.Rational.MaximalSplitTorusDescentReduction
import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSolvableEnvelopeProof
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteAssembly
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof

/-! # The two structural descent branches for smooth maximal split tori -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, the two structural descent branches hold for every smooth
connected affine group scheme. -/
theorem smoothMaximalSplitTorusDescent : SmoothMaximalSplitTorusDescentStatement.{u} :=
  smoothMaximalSplitTorusDescent_of_envelope_of_structure_of_containment
    noProperPseudoParabolicSolvableEnvelope pseudoParabolicSubgroupStructure
    (splitTorusIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
      pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
      splitSolvablePseudoCompleteFixedPoint pseudoParabolicQuotientRationalLifting)

end Langlands.GroupScheme
