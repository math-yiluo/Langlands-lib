import Langlands.Representation.RankinSelberg.HighlyRamified.MonomialGamma

/-!
# The induction on the rank for adjacent pairs

Jacquet and Shalika 1985, §4.4, prove stability for the adjacent pair `(r, r - 1)`
from stability for `(r - 1, r - 2)`, through the monomial gamma input (4.4.15). This
module runs that induction. The adjacent-rank step is a hypothesis here. Its base is
the rank-one case `UniformPairStability 1 0` from `UniformRankOneTwistStatement`, and
the monomial input at each stage is `monomialTwistGamma`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

universe uF uV uW

/-- Level-uniform stability for every adjacent pair, all spaces in `max uF uV`, from
`UniformRankOneTwistStatement` and the adjacent-rank step: stability for
`(n + 2, n + 1)` and the monomial gamma input at `n` give stability for
`(n + 3, n + 2)`. -/
theorem uniformPairStability_adjacent_of_step
    (h3 : UniformRankOneTwistStatement.{uF, max uF uV})
    (hstep : ∀ n, UniformPairStability.{uF, max uF uV, max uF uV} (n + 1) n →
      MonomialTwistGamma.{uF, max uF uV} n →
      UniformPairStability.{uF, max uF uV, max uF uV} (n + 1 + 1) (n + 1)) :
    ∀ n, UniformPairStability.{uF, max uF uV, max uF uV} (n + 1) n := by
  intro n
  induction n with
  | zero => exact uniformPairStability_rankOne h3 1
  | succ n ih => exact hstep n ih (monomialTwistGamma h3 ih)

/-- `HighlyRamifiedGammaStabilityStatement` from `UniformRankOneTwistStatement` (at the
universes `uV` and `max uF uV uW`) and the adjacent-rank step at the common universe
`max uF uV uW`. -/
theorem highlyRamifiedGammaStability_of_adjacentStep
    (h3 : UniformRankOneTwistStatement.{uF, max uF uV uW})
    (hone : UniformRankOneTwistStatement.{uF, uV})
    (hstep : ∀ n, UniformPairStability.{uF, max uF uV uW, max uF uV uW} (n + 1) n →
      MonomialTwistGamma.{uF, max uF uV uW} n →
      UniformPairStability.{uF, max uF uV uW, max uF uV uW} (n + 1 + 1) (n + 1)) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_uniformAdjacent_and_uniformRankOne
    (uniformPairStability_adjacent_of_step.{uF, max uV uW} h3 hstep) hone

end Langlands.RankinSelberg.HighlyRamified
