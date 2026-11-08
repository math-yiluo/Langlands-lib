# Splitting weighted special unitary groups over an exchange ring

This internal algebraic support unit constructs the actual group isomorphism
`Exchange.specialUnitaryEquiv` between the determinant-one isometries of the
weighted hyperbolic-plus-middle Gram form over `A × A`, with factor exchange
as scalar involution, and `Matrix.SpecialLinearGroup (Index Middle) A`.
Here `A` is any commutative ring, the middle index is finite with decidable
equality, and its universe is independent of the coefficient universe. The
middle weights `h i` have supplied unit witnesses `w i`. There is no
characteristic or anisotropy assumption, and the middle index may be empty.

`Exchange.trivialInvolution` is the identity involution on `A`, while
`Exchange.involution` exchanges the two factors of `A × A`.
`Exchange.baseForm h` has weights `h i` and trivial scalar involution;
`Exchange.form h` has weights `(h i, h i)` and factor exchange.
`Exchange.units` and `Exchange.units_val` provide the corresponding paired
unit witnesses.

The preliminary `conjugateTransposeGL` operation reverses multiplication of
invertible matrices, commutes with inverses, and squares to the identity.
It fixes the actual invertible Gram matrix because the original middle
weights are fixed by scalar conjugation. These identities prove
`unitaryTwist_involutive` for every original `DiagonalForm c Middle` with
unit middle weights, including nontrivial involutions `c`. The proof uses
the true inverse Gram matrix, without assuming that the Gram matrix is its
own inverse.

`Exchange.specialLinearProdEquiv` identifies a special-linear matrix over
the product ring with its two entrywise projections. The inverse pairs the
two matrices entrywise; determinant one is verified after both ring
projections. `Exchange.fst_conjugateTransposeSL` and its second-factor
counterpart show that scalar conjugation exchanges the projected matrices
and transposes them. The two projected `unitaryTwist` identities follow by
mapping the actual invertible Gram elements and inverse adjoints.

Consequently, a fixed pair is precisely `(g, tau(g))`, where `tau` is the
weighted inverse transpose for `Exchange.baseForm h`.
`Exchange.fixedEquiv` constructs the isomorphism between the actual
inverse-adjoint fixed subgroup and the first special-linear factor. Its
inverse uses `(g, tau(g))`, and involutivity of `tau` proves fixedness.
`Exchange.specialUnitaryEquiv` composes this with the established
`fixedSpecialUnitaryEquiv` comparison to the actual determinant-one
isometry subgroup. `Exchange.specialUnitaryEquiv_val` states that the
forward map projects the original matrix to its first coefficient;
`Exchange.specialUnitaryEquiv_symm_val` gives the entrywise paired inverse.

Provenance is internal: the construction follows from the implemented
weighted Gram and inverse-adjoint identities in `HermitianRootMatrixFixedPoints`,
the coefficient comparison in `HermitianRootMatrixNaturality`, and Mathlib's
ring maps on determinant-one matrices. It is algebraic support for splitting
the actual Hermitian group scheme after quadratic scalar extension. It does
not construct the scheme splitting, prove its geometric properties, classify
arbitrary local rank-one groups, or prove the unrestricted local
Kneser–Tits proposition.
