# Explicit inverses for shifted four-crossing maps

This internal result derives an explicit inverse from two supplied shifted
four-crossing systems. The endpoint exponents remain fixed. Its inputs are the
published shifted-window construction, Fourier uniqueness and the single-block
reciprocal-multiplier identity.

`fullMap` acts on the four-character ambient spaces. `AreInverse h k` asks
that the reverse AD, AC, BD and BC sequences multiply the corresponding forward
BC, AC, BD and AD sequences to one on each relevant parity class. No relationship
between the two recurrence shifts is needed beyond the existence of the supplied
crossing systems. The condition is symmetric by commutativity of scalar
multiplication and of character-pair parity.

In the reverse-after-forward composite, the reverse BC map cancels the forward
AD map by the reciprocal identity. The disjoint middle square then interchanges
the forward AC and BD maps. This puts the remaining three reciprocal pairs next
to each other, so each cancels by the same single-block identity. The result is
an identity on the actual ambient function spaces, not just on their compact
restrictions. The existing shifted-window landings corestrict both directions to
the two induction-block spaces, and subtype extensionality transfers the
identities. `shiftedEquiv` packages those two maps as a complex linear equivalence.

`IsGenericShift d e ζ` requires the four scalar exponent differences plus `ζ`
to avoid their rank-one exceptional sets. Negating the parameters reverses the
characters and changes the shift to `-ζ`, so the reverse genericity conditions
follow. `genericCrossing` and `genericFourCrossings` supply the input sequences
using the explicit finite-product generic multipliers. Their recurrence
parameters are the shifted differences plus one. The published opposite-parameter
scalar identity verifies `AreInverse`, giving `genericShiftEquiv` with its
opposite-shift four-crossing map as the explicit inverse.

This unit does not remove an exceptional pole or prove fixed-Lie-action
intertwining for a nonzero recurrence shift.
