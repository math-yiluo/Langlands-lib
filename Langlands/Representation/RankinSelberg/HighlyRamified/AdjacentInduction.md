# The induction on the rank for adjacent pairs

Module `Langlands.Representation.RankinSelberg.HighlyRamified.AdjacentInduction`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It runs the
induction on the rank for adjacent pairs. It also reduces the target statement to
two inputs: `UniformRankOneTwistStatement` and the adjacent-rank step. Both are
hypotheses here and are not proved.

## Provenance

Jacquet and Shalika 1985, §4.4 (printed pages 327–331), prove Proposition (4.1)
for the pair `(r, r - 1)` assuming it for `(r - 1, r - 2)`. They use the induction
hypothesis through the monomial formula (4.4.15). The case `t = 1` (§4.2, from
Proposition (2.2)) starts the induction. In Lean the ranks are `(n + 2, n + 1)`,
the step goes to `(n + 3, n + 2)`, and stability is level-uniform
(`UniformPairStability`) with all spaces in one universe.

## Main theorems

- `uniformPairStability_adjacent_of_step h3 hstep :
  ∀ n, UniformPairStability.{uF, max uF uV, max uF uV} (n + 1) n`. Assume
  `h3 : UniformRankOneTwistStatement.{uF, max uF uV}` and the adjacent-rank step
  `hstep`. The step says that `UniformPairStability (n + 1) n` and
  `MonomialTwistGamma n` give `UniformPairStability (n + 2) (n + 1)`. The proof
  is by induction on `n`. The base `UniformPairStability 1 0` is
  `uniformPairStability_rankOne h3 1` (`HighlyRamified.RankOne`). In the step,
  `MonomialTwistGamma n` is `monomialTwistGamma h3` applied to the induction
  hypothesis (`HighlyRamified.MonomialGamma`).
- `highlyRamifiedGammaStability_of_adjacentStep h3 hone hstep :
  HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}`. Assume
  `UniformRankOneTwistStatement` at the universes `max uF uV uW` and `uV`, and the
  adjacent-rank step at the common universe `max uF uV uW`. The previous theorem
  gives the adjacent case for all `n`, and
  `highlyRamifiedGammaStability_of_uniformAdjacent_and_uniformRankOne`
  (`HighlyRamified.RankOne`) gives the target.

So the target follows from proofs of `UniformRankOneTwistStatement` and of the
adjacent-rank step, the Jacquet–Shalika §4.4 analysis.
