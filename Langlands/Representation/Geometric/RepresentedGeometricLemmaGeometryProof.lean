import Langlands.Representation.Geometric.RepresentedGeometricLemmaTorusFactorConstruction
import Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Proof of the geometric prerequisites of the represented geometric lemma -/

universe u

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard V.4.5–V.4.7 for arbitrary represented parabolics: finitely many
rational double cosets, each with a representative carrying the full
geometric-lemma intersection datum. -/
theorem representedGeometricLemmaGeometry : RepresentedGeometricLemmaGeometryStatement.{u} :=
  representedGeometricLemmaGeometry_of_doubleCoset_of_parabolicDynamic
    (representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs rationalBruhat
      genericMinimalParabolic minimalParabolicConjugacy parabolicIntersectionCentralizer
      parabolicDynamic smoothMaximalSplitTorusConjugacy)
    parabolicDynamic

end Langlands.Aubert.General.RepresentedParabolic
