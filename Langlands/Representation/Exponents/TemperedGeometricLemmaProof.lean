import Langlands.Representation.Exponents.TemperedGeometricLemmaReduction
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # The geometric lemma for tempered representations (Renard VII.2.5): proof -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.5 for represented parabolics: for a tempered representation `ρ` of
`M(F)`, the unitary part `(r_Q^G i_P^G ρ)_0` is glued, in some order, from the pieces
`i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0` indexed by the double cosets `P(F) z Q(F)`. -/
theorem temperedGeometricLemma : TemperedGeometricLemmaStatement.{u, v} :=
  temperedGeometricLemma_of_structuralInputs representedGeometricLemma
    parabolicRootPresentationExistence arbitraryParabolicQuotientCompact
    arbitraryParabolicJacquetAdmissibility arbitraryParabolicJacquetAdmissibility

end Langlands.Aubert.General.RepresentedParabolic
