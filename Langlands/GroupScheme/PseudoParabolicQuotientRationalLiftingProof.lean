import Langlands.GroupScheme.Dynamic.OppositeEnvelopeLifting
import Langlands.GroupScheme.PseudoParabolicRationalLiftingAssembly
import Langlands.GroupScheme.PseudoParabolicSplitRadicalQuotientProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceProof

/-! # Rational lifting for pseudo-parabolic quotients over every field -/

universe u

namespace Langlands.GroupScheme

/-- **CGP Lemma C.2.1, rational points.** Over every field, every rational point of a
supplied quotient of a smooth connected affine group by a pseudo-parabolic subgroup
lifts to a rational point of the group. -/
theorem pseudoParabolicQuotientRationalLifting :
    PseudoParabolicQuotientRationalLiftingStatement.{u} := by
  apply PseudoParabolicSplitRadicalInduction.statement_of_trivial_split_radical
    SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence normalSubgroupQuotient
    splitUnipotentAffineTorsorStatement pseudoParabolicSplitRadicalQuotient
  intro k _ G _ _ _ N n hn hzero
  obtain hfinite | hinfinite := finite_or_infinite k
  · exact PseudoParabolicRationalLiftingAssembly.property_of_finite G
  · exact OppositeEnvelopeLifting.property_of_trivial_split_radical G n hn hzero

end Langlands.GroupScheme
