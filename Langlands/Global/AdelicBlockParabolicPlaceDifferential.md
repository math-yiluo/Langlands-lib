# Differential of the adelic parabolic half-modulus at one place

`AdelicBlockDeterminantCharacter.blockTrace B X i` sums the diagonal entries of
the ambient direction \(X\) in block \(i\). For a real curve in the real or
complex block parabolic starting at the identity, the derivative of the
determinant of its \(i\)-th Levi block is this trace. The proof differentiates
the permutation formula for the determinant. Every nonidentity permutation
moves at least two indices, so each term of its product derivative still has
a zero factor.

The real place formula takes the derivative of the positive absolute value
near determinant \(1\). The complex place formula takes the derivative of
the squared complex norm, giving twice the real part of the trace. The
square root of the pairwise block modulus is a product of these positive
determinant norms raised to `blockHalfExponent B.size i`. Differentiating this
product at the identity gives the weighted trace sum in each place formula.

These are derived differential identities for the actual adelic
half-character restricted to one place. They use the determinant comparison
in `AdelicBlockParabolicPlaceNorm` and the square-root product formula in
`BlockPrincipalSeriesNormalization`.
