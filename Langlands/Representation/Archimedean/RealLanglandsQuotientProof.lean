import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientProof
import Langlands.Representation.Archimedean.RealLanglandsFromPrincipalSeriesProof

/-!
# The Langlands classification (quotient form) for `GL_n(ℝ)`

Proof of `Langlands.Archimedean.RealLanglandsQuotientStatement`. Every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module receives a nonzero `(𝔤, K)`-intertwiner from the `O(n)`-finite
functions of the standard module of a list of real blocks of total rank `n` in Langlands order.

The proof applies the published reduction `realLanglandsQuotientReduction` to the two
published theorems it needs: Casselman's theorem in quotient form
(`realPrincipalSeriesQuotient`) and the Langlands classification starting from a
principal-series quotient (`realLanglandsFromPrincipalSeries`).
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- **The Langlands classification, existence of a Langlands quotient presentation, for
`GL_n(ℝ)`.** Every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` receives a nonzero
`(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of a list of real
blocks of total rank `n` whose exponents have non-increasing real parts. -/
theorem realLanglandsQuotient : RealLanglandsQuotientStatement.{uV} :=
  realLanglandsQuotientReduction realPrincipalSeriesQuotient realLanglandsFromPrincipalSeries

end Langlands.Archimedean
