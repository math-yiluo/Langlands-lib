# Discriminant of the symmetric component over the quadratic subfield

`Langlands.GroupScheme.KneserThree.QuatData.componentBasis` takes a basis of the underlying left module over the quaternion division algebra. The basis over the embedded quadratic field has two vectors on each division line, formed using the coefficients `1` and `j`. For an orthogonal division basis, `det_componentBasis_eq_prod_reducedNorm` computes the Gram determinant of the symmetric component as the scalar extension of the product of the reduced norms of the skew-hermitian diagonal values.

On one line write the skew-hermitian value as `ι(a) + j ι(b)`. Its first coordinate has trace zero. The symmetric component on the vector and its `j` multiple has diagonal entries `conj(b)` and `-δ b` and off-diagonal entries `conj(a)`. The determinant is `a conj(a) - δ b conj(b)`, which the embedded field identifies with the quaternion conjugate product. The reduced-norm identity gives the line contribution. Different lines are orthogonal, so the determinant of the block diagonal Gram matrix is the product of these contributions.

The formula is the explicit calculation underlying Lemma 5.1.1 in T. A. Springer's appendix to Kneser, *Lectures on Galois Cohomology of Classical Groups*, p. 106 (PDF p. 112).
