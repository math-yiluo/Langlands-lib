# Compact bounds for real block Fourier multipliers

`Langlands.Archimedean.RealBlockFourierDecay.RealBlockFourierDecayStatement`
bounds the value of `blockFrobMap` on the orthogonal group. A multiplier of
polynomial growth of degree `d` has a bound proportional to a common upper
bound for the input's order-zero and order-`d + 2` suprema on the orthogonal
group. For the latter supremum at evaluation point `g`, the repeated right
direction is the block rotation generator conjugated by `g⁻¹`.

The proof identifies differentiation in the rotation angle with that right
direction. Integration by parts over one period multiplies mode `j` by `ij`.
For each nonzero mode, applying this identity `d + 2` times bounds the weighted
coefficient by a constant times `1 / j²`. The zero mode is bounded using the
order-zero supremum. The multiplier formula for compact-finite vectors is a
finite sum and its absolute values are bounded by the convergent series of
these estimates. The companion lemma `norm_tailMultiplier_le` uses the
binomial formula for the real ascending tail and bounds its degree by the
weight parameter.

This is an internal estimate derived from the Library's block rotation,
Fourier multiplier and right derivative formulas. It supplies a compact
seminorm estimate for transporting smooth evaluation along the ascending
character quotient in the real Rankin–Selberg reduction.
