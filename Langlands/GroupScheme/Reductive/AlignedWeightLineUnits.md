# Unit discrepancies between aligned actual weight lines

Over an arbitrary commutative ring, an actual ambient group isomorphism and
an actual isomorphism of the acting coordinate tori give an isomorphism of
exponent weight modules whenever the supplied characters agree under that
torus isomorphism. The induced linear map is exactly the published differential
on the actual dual-number identity kernels. Character alignment and the torus
inclusion square are explicit premises.

If each of those modules is supplied with a trivialization by the coefficient
ring, the differential carries the chosen source generator to a unique unit
multiple of the chosen target generator. The proof composes the two
trivializations with the weight-module isomorphism. The resulting linear
automorphism of the ring is multiplication by its value at one; its inverse
provides the inverse unit. Applying the target trivialization proves the
vector equation and its uniqueness. This argument includes the zero ring and
does not require a field or local ring.

This is an internal deduction from the published actual weight-transport
results in `Rational/CrossTorusLieTransport` and the identification of exponent
weights with character weights in `Torus/ExponentCharacters`. The construction
supplies the unit discrepancies needed after root-character alignment in a
pinning comparison. It does not establish that alignment or construct a torus
point realizing prescribed simple-root units, and it does not prove local or
global pinned-comparison existence.
