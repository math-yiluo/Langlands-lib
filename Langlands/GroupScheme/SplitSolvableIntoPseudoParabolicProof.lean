import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteAssembly
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof

/-! # Rational conjugation of split solvable subgroups into pseudo-parabolics -/

universe u

namespace Langlands.GroupScheme

/-- **CGP Lemma C.2.2.** Over every field, every closed split solvable subgroup of a
smooth connected affine group has a rational conjugate contained in any given
pseudo-parabolic subgroup, through an actual group-scheme homomorphism. -/
theorem splitSolvableIntoPseudoParabolic : SplitSolvableIntoPseudoParabolicStatement.{u} :=
  splitSolvableIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
    pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
    splitSolvablePseudoCompleteFixedPoint pseudoParabolicQuotientRationalLifting

end Langlands.GroupScheme
