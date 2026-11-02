import Langlands.Representation.RankinSelberg.TwoBlockGammaConditionalAssembly
import Langlands.Representation.RankinSelberg.TwoBlockUniverseTransport
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.Representation.RankinSelberg.TwoBlockDominantRankProof
import Langlands.Representation.RankinSelberg.TwoBlockAdjacentRankProof
import Langlands.Representation.RankinSelberg.TwoBlockRankOneProof
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof

/-! Closed two-block gamma multiplicativity by the two JPSS rank descents. -/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Certified gamma multiplicativity for the actual normalized upper two-block
induction, for all positive ranks and independent carrier universes. -/
theorem twoBlockGammaMultiplicativity :
    TwoBlockGammaMultiplicativityStatement.{uF, uV, uW} :=
  twoBlockGammaMultiplicativity_of_commonUniverse
    (twoBlockGammaMultiplicativity_of_inputs_commonUniverse.{uF, max uV uW}
      normalizedProductWhittakerType
      whittakerTypeGammaConstructionInput
      equalRankFactorSwap
      twoBlockGammaDominantRank
      twoBlockGammaAdjacentRank
      twoBlockGammaRankOne
      rankOneWhittakerType)

end Langlands.RankinSelberg
