# Finite Frobenius generators of pointed Laurent subspaces

This internal construction transports the finite-variable Euclidean
algorithm in `TorusLinearization.Euclid` through `LaurentFiniteCoordinates`.
The coefficient and character-index universes are independent.

For a commutative coefficient ring and a prime `p`, `frobPower f r` is the
pointed Laurent function with underlying value `f^(p^r)`, and `frobSpan S`
is the linear span of all such powers of members of `S`.
In characteristic `p`, Frobenius stability of a subspace implies
membership of every iterated power. The finite encoding commutes with
these powers, so it maps their span to the corresponding polynomial
Frobenius span.

Over a field of characteristic `p`, `exists_finiteFrobBasis` takes a
Frobenius-stable subspace `N` contained in `finiteOrbitSpace s` for a
specified finite set `s` of primitive characters. It produces a finite
family `G` in `N` with `N = frobSpan G`. The finite encodings of `G` satisfy
`TorusLinearization.FrobIndep`, meaning that a vanishing sum of additive
one-variable polynomial substitutions has only zero substitution
polynomials.

The proof maps `N` into the finite polynomial coordinates. Its image
consists of additive polynomials and is Frobenius-stable. Applying the
existing Euclidean theorem with all variables supplies independent
generators of the image. Choosing finitely many preimages supplies `G`;
injectivity on `finiteOrbitSpace s` proves that its Frobenius span is `N`.
The field need not be perfect or infinite.

The finite-orbit containment is an explicit hypothesis. This result
does not assert that all additive functions of an algebraic group lie in
one such span, and does not construct a group-scheme isomorphism.
