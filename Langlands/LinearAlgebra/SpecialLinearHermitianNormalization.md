# Hermitian normalization of a projectively involutive outer matrix

Author: Worker 239.

This internal algebraic unit works over a field `L` of arbitrary
characteristic, a nontrivial specified field involution `c`, and a finite
nonempty matrix index type. If a nonsingular matrix `J` satisfies
`J* = a J`, then applying the adjoint twice and cancelling the nonzero
matrix gives `c(a) a = 1`.

The elementary multiplicative Hilbert 90 argument supplies a nonzero
scalar `b` with `c(b) a = b`. If `1 + a` is nonzero, take `b = 1 + a`.
Otherwise `a = -1`; choose an element `x` moved by the involution and
take `b = c(x) - x`. This argument includes characteristic two.
`hermitianScalingUnit` chooses such a unit, and `hermitianForm` has
actual Gram matrix `b J`. Semilinearity of adjoint proves this matrix
Hermitian. It is nonsingular because both factors are invertible.

Multiplying an invertible matrix by a scalar unit leaves its conjugation
unchanged after every homomorphism to a commutative coefficient ring.
The same holds for the inverse Gram matrix of `hermitianForm`.

Finally, if an invertible matrix `X` satisfies
`X θ(c(X)) = a I` for a scalar unit `a`, where `θ(Q) = (Q⁻¹)ᵀ`,
then the adjoint of `X⁻¹` is `a X⁻¹`. The proof cancels `X` in the
displayed equality and commutes its scalar factor. Thus the construction
applies to the inverse of a supplied projectively involutive outer
representative while retaining its conjugation.

All claims are elementary consequences of the imported matrix and
involution operations. This unit assumes a nontrivial involution and
the stated projective square equation; it does not construct a
quadratic field, descend an outer representative, or prove an outer
type A presentation.
