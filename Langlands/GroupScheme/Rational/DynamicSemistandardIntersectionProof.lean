import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # The general semistandard parabolic intersection theorem: proof -/

universe u

namespace Langlands.GroupScheme

/-- **General semistandard intersections** (Renard V.3.10). For two cocharacters
of a common maximal split torus of a connected reductive group over an arbitrary
field and any closed representative of the first centralizer, the pullback of the
second dynamic parabolic is parabolic with the pulled-back Levi and geometric
radical, both intersection products hold on every test scheme, and the torus
lifts semistandardly. No nesting is assumed. -/
theorem dynamicSemistandardIntersection :
    DynamicSemistandardIntersectionStatement.{u} :=
  dynamicSemistandardIntersection_of_structural parabolicDynamic
    dynamicCentralizerReductive dynamicGeometricUnipotentRadical

end Langlands.GroupScheme
