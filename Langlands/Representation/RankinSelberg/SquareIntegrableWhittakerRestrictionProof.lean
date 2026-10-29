import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionReduction
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof

/-!
# The square-integrable Whittaker restriction-square estimate

Formula (7) of JPSS 1983 §8.3: for an irreducible square-integrable representation of
`GL_r(F)`, `r = n + (0 + k + 1) + 1`, the function `‖W(diag(g, 1))‖² |det g|^(-(k+1))` is
integrable on `N_(n+1) \ GL_(n+1)(F)`. The measure theory is in
`SquareIntegrableWhittakerRestriction.of_squareIntegrableWhittakerTorusSum`; the torus
lattice square-summability it needs is `squareIntegrableWhittakerTorusSum`.
-/

namespace Langlands.RankinSelberg

universe uF uV

/-- **Formula (7) of JPSS 1983 §8.3.** -/
theorem squareIntegrableWhittakerRestriction :
    SquareIntegrableWhittakerRestrictionStatement.{uF, uV} :=
  SquareIntegrableWhittakerRestriction.of_squareIntegrableWhittakerTorusSum
    squareIntegrableWhittakerTorusSum

end Langlands.RankinSelberg
