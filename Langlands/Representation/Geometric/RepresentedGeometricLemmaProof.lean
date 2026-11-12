import Langlands.Representation.Geometric.RepresentedGeometricLemmaOrbitReduction
import Langlands.Representation.Geometric.RepresentedGeometricLemmaTorusFactorConstruction
import Langlands.Representation.Geometric.RepresentedGeometricLemmaOrbitComparisonProof
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # The geometric lemma for represented parabolics (Renard VI.5.1): proof -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.1 for represented parabolics: `r_Q ∘ i_P` is glued, in some order, from
the pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}` indexed by the finitely many double cosets
`P(F) z Q(F)`. -/
theorem representedGeometricLemma : RepresentedGeometricLemmaStatement.{u, v} :=
  representedGeometricLemma_of_geometry_and_orbitComparison
    (representedGeometricLemmaGeometry_of_doubleCoset_of_parabolicDynamic
      (representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs rationalBruhat
        genericMinimalParabolic minimalParabolicConjugacy parabolicIntersectionCentralizer
        parabolicDynamic smoothMaximalSplitTorusConjugacy)
      parabolicDynamic)
    arbitraryParabolicQuotientCompact parabolicRootPresentationExistence
    representedGeometricLemmaOrbitComparison

end Langlands.Aubert.General.RepresentedParabolic
