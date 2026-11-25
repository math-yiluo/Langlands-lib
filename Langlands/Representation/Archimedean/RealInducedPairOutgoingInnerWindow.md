# The outgoing negative inner window

Write `L = d.weight.natAbs`, `M = e.weight.natAbs`,
`P = outerWeight d e k` and `H = innerWeight d e k`.
For `IsLinkedAt d e k` and `Even (P - M)`,
`RealInducedPairOutgoingInnerWindowStatement` constructs outgoing multiplier
data on the actual source `[induced d, induced e]`. The first multiplier is
the signed multiplier at `-P` with parity `M + 1`, the last is the signed
multiplier at `-H` with parity `L + 1`, and both middle multipliers are
nonvanishing on their respective source parity classes.

If `H < 0`, this particular full four-crossing map `swap` is zero. Its first
three crossings have the inner induction window:
their central Fourier coefficients vanish for `|j| < H.natAbs` at every
compact point. The theorem `realInducedPairOutgoingInnerWindow` proves
the packaged proposition.

## Proof

The endpoint equalities give the outgoing first recurrence parameter
`1 - P`. The identity `H + L + M = P` then gives the last parameter
`1 - H`. The canonical parity makes both signed multipliers recurrent and
symmetric, and puts the two middle parameters in their generic parity classes.
The existing generic multiplier construction supplies nonvanishing middle
multipliers.

When `H < 0`, put `q = -H`. Then `q = min L M - (k + 1)` is a positive
integer strictly below both original induction weights. The final signed
multiplier is binomial, nonzero exactly on `|j| < q` in its parity class.
Its output therefore has no central modes at or above `q`.

The full outgoing map already lands in the actual exchanged source
`[induced e, induced d]`, by the published four-crossing landing theorem.
This output has high modes along either original induction rotation.
The published adjacent-rotation uncertainty theorem, with the strictly
smaller central low-mode bound `q`, forces the output to vanish.
The Fourier kernel criterion for the final binomial now says that the
preceding three-crossing output has no central modes below `q`.
The other parity vanishes by its source sign relation.

The helper `eq_zero_of_central_low` records the actual-source uncertainty
argument. The binomial helpers allow arbitrary multiplier data with the
specified last multiplier, rather than using the particular outgoing first
or middle multipliers.

## Provenance and scope

This is a derived internal consequence of the published endpoint arithmetic,
four-crossing landing, Fourier kernel criterion and adjacent uncertainty
theorem. It reuses the signed multiplier construction and the
support formulas in `RealInducedPairIncomingKernel`. No new literature claim
or classification assumption is introduced.

The window conclusion concerns the first three outgoing crossings.
It does not identify the image of the outer tail with the simultaneous
outer and inner induction conditions, prove an incoming image-kernel
equality, or establish the unrestricted two-induced-block filtration.
No vanishing of the full outgoing map is asserted when `H >= 0`.
