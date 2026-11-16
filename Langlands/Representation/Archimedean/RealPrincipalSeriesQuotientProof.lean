import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientReduction
import Langlands.Representation.Archimedean.RealPrincipalSeriesSubrepresentationProof
import Langlands.Representation.Archimedean.RealContragredientProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-!
# Casselman's theorem in quotient form for `GL_n(ℝ)`

Proof of `Langlands.Archimedean.RealPrincipalSeriesQuotientStatement`. Every irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module receives a nonzero intertwiner from the `O(n)`-finite
functions of the principal series of some `n` characters of `ℝ^×`.

The proof applies the published reduction `realPrincipalSeriesQuotientReduction` to the three
published theorems it needs: the subrepresentation theorem, the contragredient and the
principal-series duality.
-/

noncomputable section

namespace Langlands.Archimedean

universe uV

/-- **Casselman's theorem in quotient form for `GL_n(ℝ)`.** Every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` receives a nonzero `(𝔤, K)`-intertwiner from the
`O(n)`-finite functions of the standard module of some list of `n` real characters. -/
theorem realPrincipalSeriesQuotient : RealPrincipalSeriesQuotientStatement.{uV} :=
  realPrincipalSeriesQuotientReduction
    realPrincipalSeriesSubrepresentation
    RealContragredient.realContragredientStatement
    RealPrincipalSeriesDuality.realPrincipalSeriesDuality

end Langlands.Archimedean
