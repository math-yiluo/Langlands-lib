import Langlands.Representation.Archimedean.RealCharacterPairFiltration
import Langlands.Representation.Archimedean.RealInducedPairFiltrationProof

/-!
# The real Langlands classification starting from a principal-series quotient

The character-pair and induced-pair filtrations supply the adjacent step. The rank-one
reduction then gives a Langlands-ordered standard module mapping nontrivially to the
same irreducible admissible module.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- An irreducible admissible real `(𝔤𝔩_n, O(n))`-module supplied as a principal-series
quotient is a quotient of a Langlands-ordered standard module. -/
theorem realLanglandsFromPrincipalSeries : RealLanglandsFromPrincipalSeriesStatement.{uV} :=
  realLanglandsFromPrincipalSeries_of_rankOneStep
    (realRankOneStep_of_filtration realCharacterPairFiltration realInducedPairFiltration)

end Langlands.Archimedean
