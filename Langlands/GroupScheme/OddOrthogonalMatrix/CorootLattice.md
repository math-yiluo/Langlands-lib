# The actual odd coroot lattice

With at least two hyperbolic indices, the integral coroot lattice of any
actual root datum of the odd identity torus consists exactly of the
cocharacter vectors with even coordinate sum. The quotient of the full
cocharacter lattice by the coroot lattice is therefore `ZMod 2`, with
cardinality two.

The signed coroot description puts doubled short-coordinate vectors
and signed long-coordinate pairs into the even-sum lattice. Conversely,
each pair-sum and pair-difference generator is the coroot of an actual
long root. This proves equality before passing to the quotient.

The published `TypeDParityLattice` supplies the general integer lattice
and its parity quotient calculation; those definitions do not depend
on a group scheme. Its reuse here does not identify type-B roots with
type-D roots. These are internal integral calculations valid over every
field and characteristic, with no new external translation.
