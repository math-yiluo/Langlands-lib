import Langlands.Representation.Exponents.LeviInductionTemperedReduction
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # Normalized parabolic induction preserves temperedness (Renard VII.2.2): proof -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.2 for represented parabolics: if `σ` is a tempered smooth representation
of `M(F)`, in the normalized-exponent sense, then so is its normalized parabolic
induction to `G(F)`. -/
theorem leviInductionNormalizedTempered : LeviInductionNormalizedTemperedStatement.{u, v} :=
  leviInductionNormalizedTempered_reduction representedGeometricLemma
    arbitraryParabolicJacquetAdmissibility arbitraryParabolicQuotientCompact
    parabolicRootPresentationExistence

end Langlands.Aubert.General.RepresentedParabolic
