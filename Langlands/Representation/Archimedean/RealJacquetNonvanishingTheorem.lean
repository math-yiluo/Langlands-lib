import Langlands.Representation.Archimedean.RealJacquetNonvanishingProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesSubquotientProof

/-!
# Nonvanishing of the real Jacquet module

Proof of `Langlands.Archimedean.RealJacquetNonvanishingStatement`: for an irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module `V`, the subspace `𝔫V` spanned by the upper nilpotent radical is not
all of `V`. It is the reduction `realJacquetNonvanishingSubquotientReduction`
(subquotient theorem ⇒ nonvanishing) applied to Harish-Chandra's subquotient theorem
`realPrincipalSeriesSubquotient`.
-/

namespace Langlands.Archimedean

universe uV

/-- **Nonvanishing of the real Jacquet module**: `𝔫V ≠ V` for every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module `V`. -/
theorem realJacquetNonvanishing : RealJacquetNonvanishingStatement.{uV} :=
  RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction
    realPrincipalSeriesSubquotient

end Langlands.Archimedean
