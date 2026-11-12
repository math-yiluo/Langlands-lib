import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Represented Levi intersections along a common maximal split torus -/

universe u

namespace Langlands.GroupScheme

/-- Levi intersections along a common maximal split torus are represented by
an actual parabolic with its rational Levi and geometric unipotent radical. -/
theorem representedParabolicLeviIntersection : RepresentedParabolicLeviIntersectionStatement.{u} :=
  representedParabolicLeviIntersection_of_dynamic parabolicDynamic dynamicCentralizerReductive

end Langlands.GroupScheme
