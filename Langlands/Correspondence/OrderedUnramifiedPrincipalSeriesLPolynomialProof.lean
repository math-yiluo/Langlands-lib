import Langlands.Correspondence.OrderedUnramifiedPrincipalSeriesInduction
import Langlands.Representation.RankinSelberg.UnramifiedRankOneLPolynomialProof

noncomputable section

namespace Langlands.Correspondence

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The supplied L-polynomial of an ordered unramified principal series against
the trivial character of `GL₁` is its Euler polynomial. -/
theorem orderedUnramifiedPrincipalSeriesLPolynomial :
    OrderedUnramifiedPrincipalSeriesLPolynomialStatement.{uF} F :=
  OrderedUnramifiedPrincipalSeries.orderedUnramifiedPrincipalSeriesLPolynomial_of_rankOne F
    fun ψ μ z _P hP => RankinSelberg.unramifiedRankOneLPolynomial_eq F ψ μ z hP

end Langlands.Correspondence
