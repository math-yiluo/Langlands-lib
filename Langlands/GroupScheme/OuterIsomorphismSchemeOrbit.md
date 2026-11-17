# Orbits through global points of a supplied outer quotient

This is a derived, internal consequence of the supplied
`OuterIsomorphismScheme` interface. It assumes that interface, including unique
inner differences on every relative scheme test; it does not prove existence
of an outer quotient.

For a global isomorphism point `p`, `pointOrbit` is the actual morphism sending
an acting-group point to its inverse-precomposition translate of `p`.
Invariance factors this morphism through the actual outer fibre of the class
of `p`. The resulting `pointOrbitLift` is an isomorphism: the all-test orbit
axiom gives both existence and uniqueness of a point in the acting scheme
above every point of the fibre, and Yoneda detects the isomorphism.

If the outer parameter is étale over the base, its section given by the class
of `p` is an open immersion. If it is separated, the section is a closed
immersion. Pulling these sections back along the class map shows that the
fibre projection is open, respectively closed. Composing with the
isomorphism `pointOrbitLift` proves the corresponding assertion for
`pointOrbit`. These results impose no connectedness, affineness, finiteness or
nonemptiness hypothesis on the base.
