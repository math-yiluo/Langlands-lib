# The local fields of the adelic level rings

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claims on adelic levels
(`Langlands.Global.AdelicSpaceLevelTopologyStatement`). The étale-chart topology results of
Proposition 5.4 (`t2Space_etaleChartTopology`, `locallyCompactSpace_etaleChartTopology`) and
Corollary 5.7 are stated over nontrivially normed henselian valued fields. This module supplies
such structures on the completions in the level rings, compatible with their given topologies.

## Declarations

Namespace `Langlands.Global.AdelicSpaceLocalFields`.

For a Dedekind domain `A` with fraction field `F` and a height-one prime `v`:

- `rankOne`: the rank-one structure of the completed discrete valuation, with base `2`
  (`Valuation.IsRankOneDiscrete.rankOne`).
- `normedField`: the resulting nontrivially normed field structure on `v.adicCompletion F`
  (`Valued.toNontriviallyNormedField`). Its uniform structure is the valued one.
- `normedField_topology`: its topology is the given topology of the completion (`rfl`).
- `mem_adicCompletionIntegers_iff`: the completed valuation ring is the closed unit ball.
- `isUltrametricDist`, `completeSpace`: the norm is ultrametric and complete.
- `isHenselianValuedField`: the completion is a henselian valued field
  (`isHenselianValuedField_of_isUltrametricDist`).
- `henselianLocalRing`: the completed valuation ring is henselian (the Library's
  `adicCompletionIntegers_henselian`).

For an archimedean place `v` of a field `K`:

- `infiniteNormedField`: Mathlib's normed field structure on `v.Completion`, which is
  nontrivially normed because `‖2‖ = 2`.
- `infinite_isHenselianValuedField`: the completion is a henselian valued field, by the
  isometric embedding `extensionEmbedding` into `ℂ` (`isHenselianValuedField_of_isometry`).

These apply to the number-field completions `FiniteCompletion K v` (with `A` the ring of
integers) and to the curve-place completions `curvePlaceCompletion v` (with `A` the valuation
subring of the place).
