# Pole detection for squared power-trace series

`Langlands.Global.SpectralSquare.PoleDetectionStatement` takes a meromorphic
continuation of the exponential of the squared power-trace series over a
number field. It assumes convergence at a real point `σ₁`, agreement in
`Re s > σ₁`, and nonnegative orders at positive real points distinct from
`1`. Every local spectrum has positive rank and an eigenvalue of norm
at least one. Then the meromorphic order at `1` is negative. If it were
nonnegative there, the meromorphic form of Landau's theorem would imply
convergence at every positive real point. The arithmetic divergence
lemma supplies a positive point of divergence.

`crossOrder_eq_zero` applies this detection to a product of four factors.
At `1`, the first two can have at most simple poles and the third has
nonnegative order. The third and fourth have equal norms on the real ray
to the right of `1`. If the third has positive order, its norm tends to
zero along that ray, and so does the fourth's. For a meromorphic germ,
order zero gives a nonzero limit and negative order gives divergence in
norm. The fourth therefore has positive order too. The sum of the four
orders is then nonnegative, in contradiction with the detected pole.
The third factor consequently has order zero at `1`.

The product criterion abstracts the positivity argument of Peter Sarnak,
*Nonvanishing of L-functions on Re(s) = 1*, §1, display (5) (IAS manuscript
and PDF p. 3, registered `sarnak-nonvanishing-line-one`). The formal argument
uses the exponential of a series of squared power traces. Its use of
Landau's theorem is through the meromorphic extension lemma derived from
Hardy and Riesz, Theorem 10, printed p. 10 (PDF p. 26 in
`hardy-riesz-1915-dirichlet-series`).
