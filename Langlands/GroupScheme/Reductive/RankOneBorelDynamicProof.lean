import Langlands.GroupScheme.Reductive.RankOneBorelDynamicAssembly
import Langlands.GroupScheme.ProjectiveTorusFixedPointDimension
import Langlands.GroupScheme.Rational.SolvableMaximalTorusQuotientAssembly
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.SolvableProperFixedPointProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # The two dynamic Borels in semisimple rank one -/

universe u

namespace Langlands.GroupScheme

/-- In semisimple rank one, a Borel through a split maximal torus represents one
of the two opposite dynamic parabolics of any cocharacter nonorthogonal to a root.
The four structural inputs of the conditional assembly are discharged by their
published proofs. -/
theorem rankOneBorelDynamic : RankOneBorelDynamicStatement.{u} :=
  rankOneBorelDynamic_of_projectiveBorelInputs solvableProperFixedPoint
    projectiveTorusFixedPointDimension
    (solvableMaximalTorusConjugacy_of_torusQuotient solvableTorusQuotient)
    (algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
      solvableTorusQuotient)

end Langlands.GroupScheme
