# The incoming kernel before the last crossing

This internal consequence concerns the actual incoming source
`[induced e, induced d]`. It retains both induction-block Fourier conditions.
Write `L = d.weight.natAbs`, `M = e.weight.natAbs` and
`H = innerWeight d e k = k + 1 - min L M`.

For `IsLinkedAt d e k` and the canonical parity
`Even (outerWeight d e k - M)`, `RealInducedPairIncomingKernelStatement`
constructs the incoming multiplier data specified by
`RealInducedPairLinkedIncoming.exists_multiplierData`. It asserts:

- If `H <= 0`, the first crossing `to1` and the first three crossings `to3`
  are injective on the actual source.
- If `0 < H`, a source vector belongs to the kernel of `to3` exactly when
  its central Fourier coefficients vanish for `|j| < H` at every compact
  point.

The helper `to1_eq_zero_iff_of_inner_pos` gives the same exact description
for the first crossing. `realInducedPairIncomingKernel` proves the packaged
proposition. The first-crossing results apply to every multiplier datum with
the specified signed first multiplier; the three-crossing results also retain
nonvanishing of the two middle multipliers. The packaged proposition constructs
these data from the linking and parity assumptions.

## Proof

The signed first multiplier is binomial for positive `H`, a tail for negative
`H`, and the generic zero-parameter multiplier for `H = 0`. The support lemmas
`signedMultiplier_pos` and `signedMultiplier_neg` transfer the published
binomial and tail support formulas from reduced parity to the actual parity.
`signedMultiplier_zero_ne` proves nonvanishing at every integer by the generic
product formula: its numerator and denominator factors are nonzero.

For negative `H`, its absolute value is
`min L M - (k + 1)`, strictly less than both original weights. Apply
`RealInducedPairKernelRecovery.to1_injective_of_tail` using the source
`e` window. That theorem applies the published adjacent-rotation uncertainty
criterion to the actual source, whose other induction condition is also
retained. The parity relation excludes equality at the cutoff.
For `H = 0`, full nonvanishing gives injectivity on the full-character source;
compose with the inclusion of the actual source.

For positive `H`, the multiplier is nonzero exactly on the central low modes
of its parity class. The published Fourier kernel criterion identifies the
first-crossing kernel with the asserted coefficient vanishing. Coefficients
of the other parity vanish by the source sign relation.

The two middle crossings have the explicit linear equivalence
`RealInducedPairIncomingLift.middleEquiv`. Composing this equivalence with
the first crossing preserves injectivity and its exact kernel description.
This proves both alternatives for `to3`.

## Provenance and scope

The incoming multiplier construction and middle equivalence are reused
unchanged from Worker 765's work. The support, Fourier uniqueness and adjacent
uncertainty inputs are proved Library results. This is a derived internal
statement, with no new literature identification or classification premise.

The final binomial crossing is excluded from the conclusions. The statement
does not prove injectivity or nonvanishing of the full incoming swap, equality
of its range with the actual outer-tail kernel, preservation of either missing
window by a lift, or the unrestricted two-induced-block filtration.
