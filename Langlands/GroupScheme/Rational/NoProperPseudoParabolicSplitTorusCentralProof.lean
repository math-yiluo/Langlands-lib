import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSplitTorusCentralReduction
import Langlands.GroupScheme.SubgroupFunctor.NormalFactorProductExistenceProof
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceReduction
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Central split-torus images without proper pseudo-parabolics -/

universe u

namespace Langlands.GroupScheme

/-- The exact published proposition, with its structural inputs discharged. -/
theorem noProperPseudoParabolicSplitTorusCentral :
    NoProperPseudoParabolicSplitTorusCentralStatement.{u} :=
  noProperPseudoParabolicSplitTorusCentralReduction normalFactorFppfProductExistence
    (dynamicUnipotentUnipotenceReduction unitriangularUnipotent unipotentClosedSubgroup)

end Langlands.GroupScheme
