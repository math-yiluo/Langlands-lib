# Gram-isometry transport of the actual Hermitian group schemes

This derived internal construction extends the matrix transport of
`HermitianRootIsometryTransport` to the actual group schemes
`HermitianRoot.SchemeModel.groupScheme`. Let `L/k` be a separable quadratic
field extension, let `H` and `J` be diagonal forms for its nontrivial
involution on the same finite middle index set, and supply unit witnesses
for both sets of weights. An invertible matrix `P` over `L` satisfying
`conjugateTranspose (fieldInvolution k L) P * gram J * P = gram H`
induces the group-scheme isomorphism `isometryIso` from the model of `H`
to the model of `J`. The matrix `P` need not have determinant one.
The finite middle index set may be empty, and there is no characteristic
restriction, anisotropy premise or local-field premise.

For each test scheme `T` over `Spec k`, `tensorIsometryMatrix` extends `P`
along the actual inclusion of `L` into `L ⊗[k] Γ(T)`. The inclusion
respects conjugation, and every test restriction fixes the included
coefficients of `P`. Applying `gramCongruence_map` to the inclusion gives
the congruence between the actual tensor forms. Thus
`tensorIsometryEquiv` identifies their determinant-one isometry groups.
Its naturality follows from `specialUnitaryIsometryEquiv_map` and the
restriction identity for the extended matrix.

Composing with the source model's actual all-test `pointsEquiv` gives
`isometryPointsEquiv`. Its entrywise matrix naturality allows the published
`isoOfMatrixPoints` construction to produce the group-scheme isomorphism.
`isometryPointsEquiv_apply` identifies the supplied point comparison with
`tensorIsometryEquiv` applied to the source model's actual matrix. On tensor
matrix groups this equivalence is the conjugation `g ↦ P_T * g * P_T⁻¹`,
with inverse `g ↦ P_T⁻¹ * g * P_T`, by its published matrix construction.
Here `P_T` is the extended invertible matrix. This unit constructs the
scheme isomorphism from that natural point comparison; it does not add
separate evaluation theorems for its forward or inverse scheme maps.

The proof uses only the published tensor-coefficient, matrix-group and
all-test model constructions; its provenance is an internal algebraic
deduction from those definitions. A Gram isometry is supplied, not
constructed from an arbitrary Hermitian pairing. This result does not
assert that an arbitrary group has a Hermitian presentation, give a local
Hermitian dimension bound, or prove the local rank-one classification.
