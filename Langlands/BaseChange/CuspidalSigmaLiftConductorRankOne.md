# Reduction of the rank-one sigma-lift conductor identity

The rank-one instance of the Library conductor statement follows from
`SigmaLiftCharacterIdentityStatement` and `CyclicNormPullbackConductorStatement`.
The arithmetic premise is the induction formula for conductors of
quasicharacters across a cyclic field extension. It uses the Library's
principal-unit conductors on the two fields and requires continuous
models for all the twists indexed by the finite set of norm-trivial
characters. This is the exponent relation of Arthur and Clozel (1989),
Chapter 1, (6.7), at additive conductor zero, using the trace shift on
the extension.

The rank equality forces one orbit block of rank one. The published
one-block equivalence identifies the lift with that block, so the lift
is irreducible. The character-identity premise turns the distributional
lift into a Shintani lift. The character classification supplies models
of the base and lifted representations. The rank-one Shintani theorem
then identifies the lifted character as the norm pullback.

Finally, the newvector and principal-unit conductors agree for each
rank-one character model, including each determinant twist. Transporting
the arithmetic equality to the actual representation carriers and casting
to `WithTop ℕ` proves the rank-one instance.
