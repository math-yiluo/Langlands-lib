# Semilinear matrices of bases adapted to surjections

This internal unit extends the adapted-basis determinant computation to
semilinear maps over an arbitrary homomorphism of commutative rings
`g : R → R'`. Consider linear maps `f : V → W`, `f' : V' → W'`, semilinear
maps `F : V → V'`, `Q : W → W'` and a commutative square `f' ∘ F = Q ∘ f`.
Choose arbitrary linear right inverses `s` and `t` for `f` and `f'`.
The source and target right inverses need not be compatible.

The definition `semilinearKernelMap` is the induced map on the actual kernels.
For bases `b,c` of the source quotient and kernel and `b',c'` of the target
quotient and kernel, with matching source and target index types, the theorem
`adaptedBasis_semilinearMatrix` computes the coordinates of `F` on the source
adapted basis in the target adapted basis. The upper-left block is the matrix
of `Q`, the upper-right block is zero and the lower-right block is the matrix
of the induced kernel map. The lower-left block records the target kernel
projection of `F(s(b i))`.

For finite basis indices, `adaptedBasis_semilinearMatrix_det` gives the
product of the quotient and kernel matrix determinants. It follows from the
explicit matrix and the determinant formula for a triangular block matrix.
Neither semilinear map is assumed bijective, and the ring homomorphism is
arbitrary.

The provenance is internal linear algebra. The proof evaluates the source
adapted basis on the two sum-index constructors, evaluates the target split
coordinates, and uses the commutative square to obtain the zero upper-right
block. It supplies no geometric assertion.
