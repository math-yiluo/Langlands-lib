# Determinant factorization on the residue blocks

`intertwinedResidueDeterminant` proves `IntertwinedResidueDeterminantStatement`,
the character criterion used in the proof of Bushnell–Kutzko (1993),
(5.2.2)(ii), printed p. 175 (PDF p. 187). The retained source
`bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

Normalize a splitting basis so that its indices lie in one period. The
graded block maps record the action of a chain-preserving automorphism
on the lattice quotients. Automorphisms with equal blocks differ by a
depth-one unit, so the input character takes the same value on them.

Lift the invertible diagonals and elementary transvections in each block
using integral entries. Diagonal units in any coordinate have the same
character as the corresponding units in one fixed coordinate, by
intertwining with permutation matrices. The character on that coordinate
descends to the residue units because principal units act trivially on
the graded pieces. For an off-diagonal transvection within a block,
conjugation by a uniformizer in its row coordinate multiplies its entry
by the uniformizer. The result is a depth-one unit, so the transvection
has character value one. This works for every residue field, including
the field with two elements.

Diagonal and transvection generation gives a lift for each invertible
residue block. Its character is the fixed residue character evaluated
on the block determinant. Multiply these lifts to recover the original
blocks. The integral matrix of the original automorphism reduces to a
block triangular matrix, so the product of the block determinants is
the residue of the determinant of the automorphism.
