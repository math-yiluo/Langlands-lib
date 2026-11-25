# Signed discriminant of the rank-three symmetric component

Let `H` be a nondegenerate rank-three skew Gram matrix over a central division
algebra of characteristic zero. Use quaternion coordinates `Q` compatible with
the conjugation and assume the quaternion conjugate-product norm identity.
If the reduced norm of the distinguished pure quaternion `Q.x` is the reduced
norm of `H`, `ComponentSignedDiscriminantStatement` gives a basis over the
quadratic field of `Q` in which the symmetric-component determinant is the
negative of a nonzero square.

Choose an orthogonal division basis. The squared norm of its change-of-basis
matrix multiplies the reduced norm of the original Gram matrix to give the
product of the diagonal norms. The basis of the symmetric component extends
this orthogonal basis with `1` and `j` on each line, so its determinant is that
product after scalar extension. The quadratic root maps to `Q.x`, whose norm is
the negative of its square by the conjugate-product identity. The determinant
is therefore the negative square of the root times the change-of-basis norm.
Both factors are nonzero.

This is the signed discriminant calculation in Springer, appendix to M. Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), Lemma 5.1.1 and
Theorem 5.3.3(i), printed pp. 106 and 109 (PDF pp. 112 and 115).
