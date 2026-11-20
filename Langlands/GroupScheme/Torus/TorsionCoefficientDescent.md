# Coefficient descent from split-torus torsion

Worker 584. On a finite free character lattice, the map called
`torsionCoefficientMap` is reduction of exponents modulo `n` times the
lattice. It is the restriction on the group algebra for the split torus
and its `n`-torsion.

For an element of the larger coefficient ring's group algebra, the
published finite-support bound ensures that reduction of exponents
is injective on its support for sufficiently large `n`. Choose such
an `n` for which the torsion restriction descends. The coefficient of
each lifted exponent in the original ring can then be read off from
the coefficient at its exponent class in the descended restriction.
These finitely many coefficients give a preimage of the original
Laurent polynomial.

If the coefficient map is injective, preimages of elements are
unique. Taking preimages of the values of a ring map therefore
gives a unique descended ring map. This is an internal consequence of
the Library's character-lattice separation bound. It supplies
coefficient descent for an actual morphism whose torsion restrictions
are already defined over the source coefficient ring.
