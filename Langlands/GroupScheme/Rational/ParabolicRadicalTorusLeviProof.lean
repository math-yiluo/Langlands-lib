import Langlands.GroupScheme.Rational.ParabolicRadicalTorusLeviReduction
import Langlands.GroupScheme.Rational.ParabolicGeometricSolvableRadicalReduction
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusInitialLevi
import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalReduction
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # A rational Levi adapted to a maximal torus in a parabolic: proof -/

universe u

namespace Langlands.GroupScheme

/-- The intersection of a rational maximal torus with the geometric solvable radical of a
parabolic is a radical maximal torus and the largest central torus of a rational Levi,
represented by its whole-torus ambient centralizer. The six inputs of the published
assembly are supplied by published proofs: radical existence through the dynamic
Levi `Z_G(χ)`, and the centralizer Levi through the dynamic initial torus and rational
maximal-torus conjugacy in the radical. -/
theorem parabolicRadicalTorusLevi : ParabolicRadicalTorusLeviStatement.{u} :=
  parabolicRadicalTorusLevi_of_structural_inputs
    (parabolicGeometricSolvableRadicalExists_of_structure parabolicDynamic
      dynamicCentralizerReductive
      (reductiveGeometricSolvableRadicalExists_of_structure solvableRadicalExistence
        algClosedReductiveNormalSolvableTorus reductiveLargestCentralSubtorusBaseChange))
    maximalRankRadicalTorusIntersection maximalTorusBaseChange
    borelContainingSubgroupConnectedStatement
    (parabolicRadicalTorusCentralizerLevi_of_dynamic parabolicDynamic
      dynamicCentralizerReductive solvableMaximalTorusConjugacy)
    maximalTorusCentralizer

end Langlands.GroupScheme
