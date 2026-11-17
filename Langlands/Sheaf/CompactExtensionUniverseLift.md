# Compact extensions and c-softness after universe lift

This internal module provides a universe-independent local extension property
for actual ordinary module sheaves. A section near a compact set must agree on
a smaller neighborhood with a global section vanishing outside the compact
closure of that smaller neighborhood.

`universeLift` is the actual sheaf transported along the canonical lift
homeomorphism to a space in the coefficient universe.
`isCSoft_universeLift` proves the existing `CompactSoft.IsCSoft` predicate for
this sheaf from the compact extension property on the original space.

The proof represents a section along a compact set on an ordinary open, sends
the compact set down through the homeomorphism, and applies the supplied
extension property. Its lifted global extension has support contained in the
preimage of the original compact closure: outside that set its restriction to
an open neighborhood is zero. Agreement on the smaller neighborhood gives
equality of germs along the original compact set. No derived vanishing or
comparison theorem is assumed.
