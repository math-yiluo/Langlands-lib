# The compact Levi at one archimedean place

The block diagonal embedding of a product of orthogonal or unitary
groups lies in the ambient orthogonal or unitary group. The proof takes
conjugate transpose in block coordinates and uses the unitary identity
in each block. `toUnits_compactLeviEmbedding` compares this compact
embedding to `BlockShape.leviEmbedding` on invertible matrices.

For real blocks the compact inclusion in one slot agrees with
`RealLeviSlices.embK`. In particular a sign reflection in a block
becomes the ambient reflection at the corresponding consecutive
coordinate.

Each compact block determinant has norm one by taking determinants in
the unitary identity. The actual adelic half-modulus restricted to the
real or complex compact Levi is therefore one. This uses the local
determinant-norm comparison in `AdelicBlockParabolicPlaceNorm`. The two
compact comparisons identify the existing block and standard-module
conventions used in the compact Jacquet argument.
