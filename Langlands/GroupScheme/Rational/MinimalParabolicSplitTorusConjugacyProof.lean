import Langlands.GroupScheme.Rational.ParabolicTorusStatement
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Conjugacy of maximal split tori inside a minimal parabolic subgroup

The published reduction to smooth-group conjugacy is instantiated with the published
Borel–Tits conjugacy theorem (CGP Theorem C.2.3), applied to the parabolic itself.
-/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Two ambient maximal split tori factoring through a minimal rational parabolic `P`
are conjugate by a rational point of `P`, over every field. -/
theorem minimalParabolicSplitTorusConjugacy :
    MinimalParabolicSplitTorusConjugacyStatement.{u} :=
  minimalParabolicSplitTorusConjugacy_of_smoothConjugacy smoothMaximalSplitTorusConjugacy

end Langlands.GroupScheme
