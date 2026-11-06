# Fixed-exponent actual cocharacters over arbitrary bases

This internal module constructs the actual cocharacter of a standard split
torus determined by a fixed vector of integers over any base scheme. It is
the sum of the coordinate cocharacters with those integer coefficients.
On every test scheme its coordinates are the specified powers of the input
unit. Its composite with a fixed-exponent character is the multiplicative
group power map whose exponent is the integer dot product.

Every coordinate cocharacter, and hence every fixed-exponent cocharacter,
commutes with arbitrary scheme base change through the existing canonical
split-torus isomorphism. The proof tests equality after every coordinate
projection and uses the coordinate decomposition of the torus identity.
The group-map version gives precisely the dynamic cocharacter base change
used by the actual centralizer construction.

Over a field these cocharacters agree with the inverse of the existing
integral cocharacter-lattice coordinate equivalence. The existing actual
character/cocharacter pairing is therefore the integer dot product. This
allows a cocharacter chosen in a split geometric fibre to be represented
by its integer coordinates over the relative base.

The provenance is internal: the construction and proofs use the existing
coordinate characters and cocharacters, their duality and identity
decomposition, and the canonical split-torus base-change isomorphism. No
classification of all characters or cocharacters over a disconnected or
nonreduced base is asserted. No reductivity or openness theorem is claimed.
