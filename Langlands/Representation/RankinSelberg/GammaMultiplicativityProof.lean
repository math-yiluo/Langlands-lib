import Langlands.Representation.RankinSelberg.FiniteGammaMultiplicativity
import Langlands.Representation.RankinSelberg.TwoBlockGammaMultiplicativityProof

/-! Closed gamma multiplicativity for actual normalized ordered block induction. -/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- JPSS gamma multiplicativity with certified factors and independent universes. -/
theorem gammaMultiplicativity : GammaMultiplicativityStatement.{uF, uV, uW} :=
  gammaMultiplicativity_of_twoBlock
    twoBlockGammaMultiplicativity.{uF, uV, uW}
    twoBlockGammaMultiplicativity.{uF, uV, max uF uW}

end Langlands.RankinSelberg
