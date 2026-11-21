# Adjoining a skew-hermitian line

`adjoinSkewLine H c` puts a Gram matrix `H` in the upper-left block and a single diagonal value `c` in the final row and column. The other entries of the last row and column vanish. Coefficient maps commute with this construction, and a unit line added to an invertible matrix gives an invertible matrix.

With a first-kind involution the new row pairing is the original pairing on the initial coordinates plus the contribution from the last coordinate. If the original matrix is antihermitian and the line value belongs to the alternating subspace, the augmented matrix is antihermitian.

This block construction supplies the single line of prescribed value in the skew-hermitian representation argument in Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), §5.10, printed p. 96 (PDF p. 102). The matrix identities are derived by reindexing the block matrix and splitting the finite row sums.
