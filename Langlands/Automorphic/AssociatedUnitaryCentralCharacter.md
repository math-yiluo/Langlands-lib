# Unitary central characters from actual determinant matching

This internal construction supplies the unitarity deduction needed for dual
witnessed generators in `RelativeIsometryOperationStatement`. The comparison
`AssociatedCentralCharacterStatement` is an explicit proof input. This module
does not assert or prove that comparison; its exact proof remains a separate
prerequisite of the final task theorem.

For a finite-dimensional unitary representation, the invariant positive core
defines an inner product and makes each action operator a linear isometry.
`LinearIsometry.normDet_eq_one` and `LinearMap.normDet_eq_norm_det` show that its
determinant character has modulus one. This proof includes the zero-dimensional
case and uses no chosen basis.

At an arithmetic class family, the published
`RelativeWeilGroup.relativeWeilTransferReciprocity` proves surjectivity of the
actual transfer onto the idele-class group. Since `reciprocityCharacter ω` is
the inverse of the pullback of `ω` along transfer, modulus one of this pullback
forces global modulus one of `ω`. Consequently any Hecke character matching a
unitary Weil determinant is globally unitary.

Given a proof of `AssociatedCentralCharacterStatement`, weak association
provides a genuine central Hecke character with this determinant identity.
The preceding deduction proves `HasUnitaryCentralCharacter`.
`associatedUnitaryCentralCharacter` chooses such an actual character together
with proofs of global unitarity and its action on the cuspidal realization.
Field, Weil-carrier and presentation-factor universes remain independent.

The provenance is internal: this is linear algebra and a surjective-pullback
deduction from the existing concrete predicates and proved transfer theorem.
No new external literature assertion is introduced. The construction is an
intermediate result, and it does not prove the exact final isometry statement.
