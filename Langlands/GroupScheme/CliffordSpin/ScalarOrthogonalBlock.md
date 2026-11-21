# Block embeddings in the scalar orthogonal and Clifford models

For two scalar quadratic forms over a characteristic-zero field,
`scalarBlockQuadratic` gives their orthogonal sum in concatenated finite
coordinates. Its polar matrix is the corresponding block diagonal matrix.
If both initial polar matrices are invertible, the block polar matrix is
invertible by the block determinant formula.

`scalarBlockIsometryData` gives the homomorphism of actual norm-one
isometry schemes that extends the first block by identity. On any
commutative coefficient algebra, its action matrix is the block diagonal
extension of the first action matrix. The matrix preserves the block Gram
and retains the original determinant. The construction takes the unique
point in the range of the norm-one coordinate homomorphism, proves
naturality, and represents the resulting map of affine points.

`scalarBlockSpin` gives the corresponding block extension on the affine
Clifford lift schemes. The isometry from the product quadratic space to
the concatenated coordinate space carries the product basis to the
standard basis. The Clifford extension and that basis comparison give
the displayed action matrix formula for the composite.

These constructions supply the block maps used in the spin stabilizer
argument of Kneser, *Lectures on Galois Cohomology of Classical Groups*
(1969), §§5.9–5.10, pp. 93–95.
