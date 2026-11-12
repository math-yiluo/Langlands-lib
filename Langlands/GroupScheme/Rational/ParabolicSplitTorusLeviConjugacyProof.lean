import Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Rational conjugation of a parabolic split torus into a supplied Levi -/

universe u

namespace Langlands.GroupScheme

/-- A maximal split torus contained in a parabolic can be conjugated into its
supplied rational Levi by a rational point of that parabolic. -/
theorem parabolicSplitTorusLeviConjugacy : ParabolicSplitTorusLeviConjugacyStatement.{u} :=
  parabolicSplitTorusLeviConjugacyStatement_of_dynamic_and_smoothConjugacy
    parabolicDynamic smoothMaximalSplitTorusConjugacy

end Langlands.GroupScheme
