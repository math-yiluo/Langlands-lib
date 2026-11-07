# Integral supporting cocharacters for finite character cones

This internal derived construction concerns a finite family of actual characters
of an actual split torus over an arbitrary field. A nonnegative combination in
the real character space is assumed to have no expansion with every coefficient
strictly positive. The construction gives a genuine integral cocharacter whose
pairings with the family are all nonnegative and include a positive value.
Every character having positive coefficient in the given expansion has zero
pairing with this cocharacter. The family may contain repeated or dependent
characters.

The proof uses the finite-cone supporting-functional theorem and the perfect
real character/cocharacter pairing of a split torus to obtain a real
cocharacter. Nonnegativity and the zero value of the total combination force
zero pairing with each character having positive coefficient. Integral
sign realization is then applied simultaneously to the positive and negative
evaluation functionals of every character. Both signs are required to retain
zero pairings as well as nonnegative and positive pairings. The chosen
`boundaryCocharacter` is an element of the original torus's cocharacter lattice,
with these properties given by `boundaryCocharacter_spec`.

This supplies the lattice step for the boundary argument toward Renard VII.2.4.
It does not assert that the cocharacter defines a proper parabolic containing a
given original parabolic, or that a given Jacquet exponent becomes unitary.
