# Exponential domination in the two-block real torus

`rootPos x` is the sum of the positive parts of the simple-root differences `x_i - x_{i+1}`.

* `blockLog_last`: the last ambient coordinate of `blockLog y z` belongs to the tail block.
* `exponent_le`, `exponent_le_first`: the sum of the positive coordinates of `blockLog y z` is
  bounded by the rank times `rootPos` plus the positive part of the last coordinate (telescoping
  to the last coordinate); a large positive exponent on the first block controls its negative
  coordinates.
* `torusEnvelope hkn A B T J P Q (y, z) = exp(A Σ|y_i| + B Σ|z_j| + T Σ y_i - J rootPos x
  - P max(x_last, 0) - Q max(-z_0, 0))` with `x = blockLog y z`.

`RealGapTorusBoundStatement`: if `B ≥ 0`, `A + 1 ≤ T`,
`max(2T, B+1)(r+1) + (B+1)(r+1-k) ≤ J`, `max(2T, B+1)(r+1) ≤ P` and `(B+1)(r+1-k) ≤ Q`, then
`torusEnvelope` is integrable for product Lebesgue measure. `realGapTorusBound` proves it by
bounding the envelope by the product of the integrable exponentials `exp(-Σ|y_i|)` and
`exp(-Σ|z_j|)`.

`RealTwoBlockHaar.blockLog` and the complex two-block chart both concatenate real
logarithmic coordinates. The estimate and its proof are shared with `ComplexGapTorusBound`.
It gives the toral majorant for the convergence estimates of Jacquet, *Archimedean
Rankin–Selberg Integrals* (2009), §10.1, Lemma 10.1.
