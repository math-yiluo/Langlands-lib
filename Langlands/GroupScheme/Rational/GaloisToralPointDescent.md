# Descent of a maximal torus that centralizes a Galois point

`Langlands.GroupScheme.GaloisToralPointDescentStatement` starts with a
point of an affine group over a finite Galois extension. Assume its
centralizer on all tests is a maximal torus over the extension, and each
coefficient automorphism fixes or inverts the point. The point factors
through a maximal torus defined over the base field.

After changing the coefficient structure on a test scheme, a constant
point is evaluated using the corresponding automorphism. Commuting
with an element is equivalent to commuting with its inverse, so these
changes preserve the subgroup functor given by the centralizer. The
Library's Galois descent then gives a maximal torus over the base and
an isomorphism that recovers its inclusion over the extension. The
original point commutes with itself, and this isomorphism transports
its factorization through the centralizer to the descended torus.
