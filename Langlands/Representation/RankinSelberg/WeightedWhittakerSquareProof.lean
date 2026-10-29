import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareReduction
import Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionProof

/-!
# The weighted Whittaker square estimate

JPSS 1983 §8.3: for an irreducible square-integrable representation of `GL_(n+1)(F)`,
both weighted Whittaker squares `‖W(x)‖² ‖Φ(e_(n+1) x)‖² |det x|^(2a)`, `a > 0`, are
integrable on `N_(n+1) \ GL_(n+1)(F)`, for the standard and for the inverse character.
The argument is `weightedWhittakerSquare_of`; it uses the recursive quotient integration
formula `recursiveQuotientIntegration` and the restricted Whittaker square estimate
`squareIntegrableWhittakerRestriction`.
-/

namespace Langlands.RankinSelberg

universe uF uV

/-- **The weighted Whittaker square estimate of JPSS 1983 §8.3**, for both character
signs. -/
theorem weightedWhittakerSquare : WeightedWhittakerSquareStatement.{uF, uV} :=
  weightedWhittakerSquare_of (fun F T m => recursiveQuotientIntegration F T m)
    squareIntegrableWhittakerRestriction

end Langlands.RankinSelberg
