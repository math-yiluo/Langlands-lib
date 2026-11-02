import Langlands.Representation.RankinSelberg.TwoBlockLVerifiedInputAssembly
import Langlands.Representation.RankinSelberg.TwoBlockDominantRankProof
import Langlands.Representation.RankinSelberg.TwoBlockAdjacentRankProof
import Langlands.Representation.RankinSelberg.TwoBlockRankOneProof
import Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityProof
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The closed two-block L-polynomial theorem in every rank order, with
independent field, test-carrier and dependent block-carrier universes. -/
theorem twoBlockLFactorMultiplicativity :
    TwoBlockLFactorMultiplicativityStatement.{uF, uV, uW} :=
  TwoBlockLVerifiedInputAssembly.twoBlockLFactorMultiplicativity_of_remainingInputs
    twoBlockLDominantRank.{uF, max uF uV uW, max uF uV uW}
    twoBlockLAdjacentRank.{uF, max uF uV uW, max uF uV uW}
    twoBlockLRankOne.{uF, max uF uV uW, max uF uV uW}
    rankOneExtensionLDivisibility.{uF, max uF uV uW, max uF uV uW}
    whittakerTypeHighlyRamifiedLVanishing.{uF, 0, max uF uV uW}

end Langlands.RankinSelberg
