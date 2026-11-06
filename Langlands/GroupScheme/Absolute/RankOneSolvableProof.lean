import Langlands.GroupScheme.Absolute.RankOneAlgebraicClosureReduction
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.RankOneBorelDynamicProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # The rank-one obstruction for smooth connected solvable subgroups -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected solvable closed subgroup through a split maximal torus
cannot meet both of a pair of opposite root spaces nontrivially in its Lie image.
All geometric inputs of the arbitrary-field reduction are supplied by proofs. -/
theorem rankOneSolvableObstruction : RankOneSolvableObstructionStatement.{u} := by
  refine rankOneSolvableObstruction_of_geometricStatements
    rankOneBorelDynamic.{u} dynamicCentralizerReductive.{u}
    centralizerBorelIntersection.{u} ?_
  intro k K _ _ _ G _ _ T i hi
  exact (maximalTorusBaseChange.{u} k K G T i hi.1 hi.2.1).mp hi

end Langlands.GroupScheme
