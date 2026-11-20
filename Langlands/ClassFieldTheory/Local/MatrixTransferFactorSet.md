# The matrix factor set for tensor corestriction

This is the matrix calculation relating the tensor descent to the
cohomological transfer used in Serre, *Local Fields*, Chapter XI, §2.
It uses the positive descent factor-set convention of Chapter X, §5.
The tensor construction, coefficient action and coset convention come
from the Library's Brauer corestriction and Tate transfer modules.

A family of invertible matrices induces an invertible indexed Kronecker
matrix. Its unit scalar is the product of the respective unit scalars,
and the permutation matrix for the left coset action reindexes its
factors. For an automorphism `g`, the lift combines the Kronecker product
of conjugates of the subgroup lifts with this permutation matrix. The
Schreier product identity identifies the subgroup factor for `g*t` with
the product of the two successive subgroup factors. Multiplying the two
tensor lifts with the coefficient action therefore gives the lift for
`g*t` times the product of the conjugates of the lower scalar defects.
This computes the scalar defect for the given lift family.
