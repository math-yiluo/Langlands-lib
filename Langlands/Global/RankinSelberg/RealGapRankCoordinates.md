# Consecutive coordinates of the real unequal-rank kernels

This module is the real counterpart of the Library's `ComplexGapRankCoordinates`. It identifies the
padding, lower rectangle and Weyl element of the Library's real local zeta integrals
(`ArchimedeanLocal.rectangularPoint`, `ArchimedeanLocal.unfoldingWeyl`) with the consecutive block
coordinates of the gap charts.

* `rankLT t m : t < t + 1 + m`.
* `rectangleRows t m` reindexes the rows of an `(t + 1 + m − (t + 1)) × (t + 1)` matrix as an
  `m × (t + 1)` matrix; `measurePreserving_rectangleRows`: it preserves the rectangular product measure.
* `padGL_eq_consecutive`: padding `g ∈ GL_{t+1}(ℝ)` to `GL_{t+1+m+1}(ℝ)` is `diag(diag(g, 1_m), 1)`.
* `rectangularPoint_eq_consecutive`: the point `rectangularPoint g X` of the larger pair equals
  `diag(diag(g, 1_{q+1}) · lowerShear(rectangleRows X), 1)`.
* `rectangularPoint_eq_lowerPoint`: the point of the smaller pair is `lowerPoint g (rectangleRows X)`,
  the lower block with a zero row appended (`RealGapDualArguments`).
* `unfoldingWeyl_eq_consecutive`: `unfoldingWeyl (rankLT t m) = tailWeyl (t + 1) (m + 1)`.
* `tailWeyl_mul_self` and `inverseTranspose_tailWeyl`: the tail Weyl element is an involution fixed by
  inverse transpose.

The proofs compare matrix entries of the block constructions (`lowerBlockLocalization`,
`lowerBlockPair`, `blockSum`) after reindexing. These identities place the chart computations of
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.2, at the points of the local integrals of
its §2.
