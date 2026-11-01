import Langlands.Representation.RankinSelberg.AdjacentRankLowerCharacterL
import Langlands.Representation.RankinSelberg.TwoBlockAdjacentRankGammaFromTransport
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The adjacent-rank gamma base with the original complete upper-family conclusion. -/
theorem twoBlockGammaAdjacentRank : TwoBlockGammaAdjacentRankStatement.{uF,uV,uW} :=
  twoBlockGammaAdjacentRank_of_transport.{uF,uV,uW} unramifiedTwistGamma.{uF,uV,uW}

/-- The adjacent-rank L base with the original complete upper-family conclusion. -/
theorem twoBlockLAdjacentRank : TwoBlockLAdjacentRankStatement.{uF,uV,uW} := by
  intro p hp F ψ ν r t m h V hVadd hVmod W hWadd hWmod π σ ht hm₀ hπ hσ
  let := F.canonicalTopologicalData.topology
  exact Padic.adjacentRankUpperL_of_lowerCharacter F ψ ν.val r t m h π σ ht hm₀ hσ
    (fun σ₁ χ hσ₁ => Padic.adjacentRankLowerCharacterL F ψ ν.val ν.property
      σ₁ π hσ₁ hπ χ)

end Langlands.RankinSelberg
