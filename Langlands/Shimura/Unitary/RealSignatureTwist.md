# Prescribing all real signatures by a symmetric unit

At each real embedding the algebra has its complex matrix coordinates
and its original Hermitian Gram matrix H. In those coordinates,
H⁻¹J is fixed by the adjoint for H, where J is the prescribed signature
matrix. Twisting by H⁻¹J would give Gram matrix J at that place.

The finite-dimensional real matrix coordinates are continuous in the
scalar extension of a basis of the original algebra. Weak approximation
provides one global element whose coordinates, after averaging with its
image under the involution, put every twisted Gram matrix in the open
neighborhood of its prescribed signature. The congruences make the
symmetric element invertible at each real embedding. Faithful scalar
extension and the finite-dimensional left multiplication map reflect
invertibility back to the original algebra.

`realSignatureTwist` uses this symmetric unit to twist the original
involution. At each real embedding the resulting Gram matrix is
congruent to the prescribed one, so the change of basis gives the
actual involution-preserving equivalence asserted by `HasSignature`.
