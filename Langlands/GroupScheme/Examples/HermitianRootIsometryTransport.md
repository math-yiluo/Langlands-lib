# Isometry transport of actual Hermitian matrix groups

This derived internal unit uses an invertible matrix `P` satisfying the actual
Gram congruence `conjugateTranspose c P * gram J * P = gram H`. Conjugation
`g ↦ P * g * P⁻¹` identifies `specialUnitarySubgroup H` with
`specialUnitarySubgroup J`. The inverse is conjugation by `P⁻¹`.

The construction is over any commutative ring and any specified ring involution.
The change-of-basis matrix need not have determinant one, the diagonal weights
need not be units, and no characteristic restriction is imposed. The index set
is finite and can be empty.

The proof reverses a Gram congruence by multiplying with the inverse matrix.
The conjugate-transpose product identity then proves preservation of the new
form under conjugation. Determinants cancel, so determinant-one matrices remain
determinant one. The coordinate formulas follow from the construction.

`gramCongruence_map` extends the congruence along every coefficient
homomorphism compatible with the two involutions and both sets of weights.
`specialUnitaryIsometryEquiv_map` proves that this coefficient change commutes
with the group equivalence. These are identities of the actual matrix groups,
using the published `PreservesForm`, `specialUnitarySubgroup` and
`specialUnitaryMap` definitions. No classification or local arithmetic result
is assumed.

This unit constructs transport between matrix groups for a supplied invertible
Gram congruence. It does not construct that congruence from an arbitrary
Hermitian pairing, extend this transport to a group-scheme isomorphism, prove
existence of a Hermitian presentation of an arbitrary group, or prove the local
rank-one classification.
