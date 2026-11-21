# Satake evaluation of a spherical two-block constant term

Assume a finite expansion of the normalized radical integral as a sum of
products of spherical functions on the two blocks. The ambient Satake
character at an ordered tuple evaluates this sum by applying each block
Satake character to its factor and multiplying. Each block receives the
tuples of entries at its own consecutive coordinates.

The proof integrates the ambient function against the normalized spherical
section. The volume-one parabolic integration formula applies because both
factors are right spherical-invariant. On the parabolic, the section factors
into the block sections and the half modulus, so Fubini identifies the
radical integral with the given expansion. Integrability of each block
function times its section gives the convergent product integrals used to
evaluate the expansion.

This is the character evaluation used for constant-term compatibility with
base change in Laumon (1996), 4.2.4. The Lean result accepts the pointwise
expansion as a premise on the existing coordinates and normalized Haar
measures.
