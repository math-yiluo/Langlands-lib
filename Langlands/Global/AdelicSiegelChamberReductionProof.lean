import Langlands.Global.AdelicChamberFromRankOneHeight
import Langlands.Global.AdelicRankOneOrbitHeightBoundProof

/-! # The chamber form of Springer's fundamental set theorem

See the paired Markdown file for the statement and the proof. -/

noncomputable section

universe u

namespace Langlands.Global.AdelicSiegelFactors

open RepresentationGrowth

/-- **The chamber form of Springer's fundamental set theorem** for the actual adelic Siegel
setup: for every connected reductive group over a number field, every actual algebraic
Siegel setup and every compact subgroup `K` with `P(𝔸_F) K = G(𝔸_F)`, there is a positive
threshold `t` such that every norm-one point has a rational left translate `n m a k` with
`n ∈ N(𝔸_F)`, `m ∈ M(𝔸_F)¹`, `a` in the weak chamber `A_{T₀}(t)` and `k ∈ K`. -/
theorem adelicSiegelChamberReduction : AdelicSiegelChamberReductionStatement.{u} :=
  adelicSiegelChamberReduction_of_rankOne_height rankOneParabolicRationalOrbitHeightBound

end Langlands.Global.AdelicSiegelFactors
