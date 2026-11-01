import Langlands.Representation.RankinSelberg.AdjacentRankLowerCharacterGamma

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The exact adjacent-rank gamma target follows from complete unramified gamma
transport, retaining the latter as an explicit undischarged premise. -/
def AdjacentRankGammaFromTransportStatement : Prop :=
  UnramifiedTwistGammaStatement.{uF,uV,uW} →
    TwoBlockGammaAdjacentRankStatement.{uF,uV,uW}

/-- The lower analytic product transports through the actual reversal of the
ordered dependent block family. -/
theorem twoBlockGammaAdjacentRank_of_transport :
    AdjacentRankGammaFromTransportStatement.{uF,uV,uW} := by
  intro H p hp F ψ ν r t m h V hVadd hVmod W hWadd hWmod π σ ht hm₀ hπ hσ
  let := F.canonicalTopologicalData.topology
  exact Padic.adjacentRankUpperGamma_of_lowerCharacter F ψ ν.val r t m h π σ ht hm₀ hσ
    (fun σ₁ χ hσ₁ => Padic.adjacentRankLowerCharacterGamma_of_transport F H
      ψ ν.val ν.property σ₁ π hσ₁ hπ χ)

end Langlands.RankinSelberg
