import Langlands.Automorphic.StableTwist.Assembly
import Langlands.Automorphic.StableTwist.ArithmeticDeepTwist
import Langlands.Representation.RankinSelberg.PairGammaTwistExchangeProof
import Langlands.Automorphic.PrincipalSeriesGammaMatchProof

/-! # Stable pair gamma comparison under highly ramified twists: proof

The conditional assembly `stableTwistPairGammaMatch_of` combined with the proofs of its three
inputs: the twist exchange of JPSS pair gamma factors, arithmetic stability of pair gamma
factors under highly ramified twists, and the principal-series comparison.
-/

noncomputable section

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE

/-- **Stable pair gamma comparison** (Henniart 1986, Lemma 4.2 and §4.3). -/
theorem stableTwistPairGammaMatchStatement :
    StableTwistPairGammaMatchStatement.{u, uV, uE} :=
  Automorphic.StableTwist.stableTwistPairGammaMatch_of
    RankinSelberg.pairGammaTwistExchange.{u, u, u}
    ArithmeticStableTwist.arithmeticStableTwistGamma.{u, uV, uE}
    principalSeriesPairGammaMatchStatement.{u, uV, uE}

end Langlands.ClassField.Global.RelativeWeilGroup
