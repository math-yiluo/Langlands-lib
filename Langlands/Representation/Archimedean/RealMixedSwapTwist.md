# Signed reversal on real rank-three function spaces

This internal helper for the mixed real block swap uses
`w = [0,0,1; 0,-1,0; 1,0,0]` and the smooth inverse-transpose automorphism
`theta(g) = (gᵀ)⁻¹` of `GL₃(ℝ)`. The matrix `w` is orthogonal, has determinant
one, and satisfies `w² = 1`. The map `twist(g) = w theta(g)` is an involution.

The implemented proofs check the fixed matrix identities entry by entry,
use transposition and the group inverse for the inverse-transpose identities,
and use the open embedding of the units into matrices for smoothness.
Inverse transpose fixes `O(3)` pointwise. Thus pullback `twistLin` commutes with
right orthogonal translation. The finite-dimensional orthogonal orbit span
of the pullback lies in the linear image of the original orbit span.

For `p : Fin 2`, `wMat_rotationGenerator` checks
`w X_p w = X_(1-p)` entry by entry. Conjugation commutes with the matrix
exponential, giving `w_blockRotation_w`. Consequently
`twist(r_p(t) g) = r_(1-p)(t) twist(g)`. Substituting this identity into the
definition of the interval integral proves
`blockFourierCoefficient_twistLin`: the coefficient with index `k` in
plane `p` of the pullback equals the coefficient with the same index in
plane `1-p` of the original function at `twist(g)`. This identity requires
no continuity or integrability assumption, since its integrands agree.

These facts concern function spaces. This module does not yet assert that
the pullback carries any particular pair of standard modules to each other,
or that it is a Lie intertwiner.

Provenance: derived internal linear algebra and function-space facts, adapting
the project’s `ComplexReverseTwist` construction to a determinant-one real
signed reversal. No external mathematical assertion is assumed.
