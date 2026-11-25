# Actual jet basis matrices under affine restriction

This module proves determinant formulas for the actual restrictions
between affine sections of the identity jets of a smooth affine group scheme
`G` over an arbitrary scheme `S`.

Fix an inclusion `V ≤ U` of affine base opens, cotangent bases `bU,bV` with
the same finite index type `σ`, and augmentation-ideal lifts `zU,zV` of those
bases. These are bases of the actual augmentation cotangents already
identified with the affine sections of `G.cotangentAtIdentity`. The lifts on
the two opens need not be restrictions of one another.
`cotangentRestrictionMatrix` is the matrix in `bV` of the intrinsic
augmentation-cotangent restriction applied to `bU`. The earlier restriction
comparison identifies it with the actual cotangent sheaf restriction.

`functionRestriction_algebraMap` uses naturality of the actual structural
morphism to compare coefficient restrictions.
`functionRestriction_aeval` then proves that restriction commutes with
polynomial evaluation after restricting all coefficients.
`layerRestriction_layerBasis` applies this to each homogeneous monomial.
The coefficient map sends the monomial with coefficient one over `U` to the
same monomial with coefficient one over `V`.

`layerRestriction_layerBasis_action` proves that the restricted actual layer
vector is obtained by the homogeneous polynomial action of
`cotangentRestrictionMatrix`. For each column, the linear form whose
coefficients are given by the target cotangent basis evaluates to a lift of
the restricted source cotangent vector. Lift independence and the general
homogeneous-substitution compatibility therefore apply, without requiring
the restricted source vectors to be a basis over the target ring.
`layerBasis_restrictionMatrix` gives the resulting matrix equality and
`layerBasis_restrictionMatrix_det` applies the arbitrary-ring homogeneous
determinant formula.

Finally choose any families of linear sections of the actual jet truncations
over `U` and `V`. The theorem `totalBasis_restrictionMatrix_det` states that
the matrix, in the target total adapted basis, of restriction applied to the
source total adapted basis has determinant

`det(cotangentRestrictionMatrix) ^ jetExponent σ n`.

The proof uses the order-zero scalar basis and then induction on jet order.
The actual restriction square commutes with truncation. The generic
semilinear split-basis theorem consequently expresses each successive
determinant as the product of the lower-jet and layer determinants. The two
families of sections are arbitrary and unrelated. The previously defined
exponent is positive when the jet order is positive, including its documented
empty-variable convention.

The provenance is internal: the result combines the actual sheaf
restriction comparisons, augmentation-layer coordinates and arbitrary-ring
homogeneous determinant calculation. The same-index hypothesis concerns
the two supplied affine bases only; this module asserts neither a global
constant-rank condition nor the existence of these bases on every affine.
It supplies the restriction determinant calculation for later line-bundle
gluing. It does not construct that line isomorphism or prove ampleness.
