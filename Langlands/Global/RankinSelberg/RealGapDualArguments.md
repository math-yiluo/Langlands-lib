# Matrix arguments in the split real dual Godement integral

This module is the real counterpart of the Library's `ComplexGapDualArguments`. Notation as in
`RealGapDualChart`: `n = k + q + 1`, `ι` and `ι₁` are the inverse transposes of `GL_n(ℝ)` and
`GL_k(ℝ)`, `A = diag(·, 1_{q+1})` is the leading block inclusion and `w = tailWeyl k (q+1)`.

* `leading C` is the `n × k` matrix of the first `k` columns of `C ∈ GL_n(ℝ)`, and `tailColumn C j` is
  column `k + j` of `C`.
* `dualMatrix C h V = ι(C) · w · lowerShear(−extendLower V) · A(ι₁ h)` is the integrating matrix of the
  dual chart of `RealGapDualChart` for fixed retained data `C`, leading variable `h` and
  `q × k` rectangle `V`.
* `lowerPoint g V = [[g, 0], [extendLower V, 1]]` is the smaller-rank lower block whose last row is the
  last standard row.
* `shearRectangle h V X` is the `(q+1) × k` matrix `X − extendLower(V) · ι₁(h)` with its rows reversed.

`RealGapDualArgumentsStatement` (proved by `realGapDualArguments`): for all `C`, `g`, `h`, `V` and a
`(q+1) × k` matrix `X`,

* `leadingArgument`: `leading(dualMatrix C h V · lowerShear X) =
  ι(C) · stack(ι₁(h), shearRectangle h V X)`, the stack of an `k × k` block above a `(q+1) × k` block;
* `tailArgument`: `tailColumn(dualMatrix C h V · lowerShear X, j) = tailColumn(ι(C), q − j)`;
* `lastFrequency`: the last row of `A(g) · (dualMatrix C h V)^{-1}` is `tailColumn(C, 0)`;
* `whittakerArgument`: `A(g) · (dualMatrix C h V)^{-1} = lowerPoint(g · ι₁(h)^{-1}, V) · w · ι(C)^{-1}`.

`measurePreserving_shearRectangle`: for an additive Haar measure `μ` on `ℝ`, `shearRectangle h V`
preserves `rectangularMeasure μ (q+1) k`, being a translation followed by a reversal of the rows.

The proof multiplies the two lower block shears and the embedded leading matrix in consecutive block
coordinates (`lowerBlockPair`). The lower block fixes the tail columns. Its last row is the last
standard row, so the tail reversal `w` moves the last frequency to the first tail column of `C`.
This is the change of variables between (10.7) and (10.9) in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §10.3.
