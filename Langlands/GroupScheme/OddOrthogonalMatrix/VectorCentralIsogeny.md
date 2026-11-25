# The actual split type-B vector central isogeny

A connected reductive field group with a supplied split maximal torus,
finite reduced root datum with full coroot span, and numbered type-B
Cartan matrix admits an actual central isogeny to the identity component
of the split odd norm-one isometry group. The construction also records
the compatible torus map and its exact character image: the integral
root lattice of the supplied datum.

The preceding integral vector root-datum morphism is realized by the
published split central-isogeny existence theorem. The actual torus
pullback equals that morphism's character map, transferring its exact
image calculation. The central-isogeny predicate retains its full
scheme-theoretic kernel, finiteness, flatness and surjectivity meanings.
Every character in the torus image is separately shown to kill the full
kernel on arbitrary test schemes, including nonreduced schemes.

This module uses internal root-datum and actual-group realization results.
The two supporting new modules compute the odd coroot parity quotient
and construct the injective numbered root-datum morphism; their paired
Markdown describes those proofs. The field and characteristic remain
unrestricted. The codomain here is the identity component. That
component is identified with the full odd norm-one group in
`OddOrthogonalMatrix.FullVectorCentralIsogeny`, and the split
presentation is descended in `SimplyConnected.TypeBVectorQuotient`.
