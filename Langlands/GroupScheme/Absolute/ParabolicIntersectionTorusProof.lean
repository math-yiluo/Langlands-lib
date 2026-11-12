import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.Absolute.ParabolicIntersectionGeometryProof
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # A common rational maximal torus for two parabolic subgroups -/

universe u

namespace Langlands.GroupScheme

/-- **Borel–Tits, Proposition 4.7, first assertion.** Two rational parabolic subgroups of
a connected reductive group over any field contain a common maximal torus defined over
the ground field, with actual factorizations through both parabolics. -/
theorem parabolicIntersectionTorus : ParabolicIntersectionTorusStatement.{u} :=
  parabolicIntersectionTorus_of_structural_inputs maximalTorusExistence
    maximalTorusBaseChange maximalTorusConjugacy parabolicIntersectionGeometry

end Langlands.GroupScheme
