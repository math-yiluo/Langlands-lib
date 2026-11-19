# Weight bases for scalar-extended exterior representations

`MatrixRepresentation.reindexedExteriorBasis` is a basis in the finite
coordinates of a reindexed exterior power. Its vectors are the columns of
the inverse of the exterior power of the original basis coordinate matrix,
with the rows and columns reindexed by the supplied equivalence.

`SplitPinning.reindexedExteriorBasis_mem_representationWeightSpace` shows that
if the original basis vectors have specified weights after scalar extension,
each exterior basis vector has the sum of the weights in its index subset.
The proof works on every affine test algebra. The original basis diagonalizes
the torus matrix. Taking exterior powers gives products of the selected
diagonal entries, which evaluate the corresponding sums of characters.
Reindexing and the affine base-change formulas identify the resulting matrix
with the action of the ground-field exterior representation. The columns
of the inverse coordinate matrix then give the required eigenvectors.

This is a derived coordinate construction from the Library's exterior
matrix formulas and its all-affine-test definition of weight spaces.
