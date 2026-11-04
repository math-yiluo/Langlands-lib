import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSolvableEnvelopeReduction
import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSplitTorusCentralSmoothReduction
import Langlands.GroupScheme.Rational.UnipotentQuotientSplitTorusPreimageProof
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceReduction
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProduct
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof

/-! # Common solvable envelope without proper pseudo-parabolic subgroups -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected affine group over a field with no proper pseudo-parabolic subgroup has one
smooth connected affine solvable closed subgroup containing every split subtorus. -/
theorem noProperPseudoParabolicSolvableEnvelope :
    NoProperPseudoParabolicSolvableEnvelopeStatement.{u} :=
  noProperPseudoParabolicSolvableEnvelope_of_statements unipotentRadicalExistence
    unipotentRadicalQuotient
    (noProperPseudoParabolicSplitTorusCentral_of_smooth_statements
      smoothConnectedNormalFactorFppfProductExistence
      (dynamicUnipotentUnipotenceReduction unitriangularUnipotent unipotentClosedSubgroup))
    unipotentQuotientSplitTorusPreimageStatement

end Langlands.GroupScheme
