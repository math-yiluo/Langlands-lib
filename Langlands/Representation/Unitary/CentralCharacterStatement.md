# Unitary central characters from invariant positive forms

`Langlands.UnitarizableCentralCharacterStatement.{uG,uV}` states that every
irreducible admissible unitarizable complex representation of an arbitrary
topological group admits the existing `Langlands.UnitaryCentralCharacter`
datum. It is a proposition definition; this module supplies no proof.

The group `G : Type uG` and carrier `V : Type uV` have independent universes.
The input consists of a group topology compatible with multiplication and
inversion, a complex module carrier, the actual representation, and its three
predicates `IsAdmissible`, `Representation.IsIrreducible`, and
`IsUnitarizable`. No local compactness or finite dimension is assumed. No norm,
topology, completion, invariant form, scalar-action witness, or central
character is supplied on the carrier. Irreducibility implies that the carrier
is nonzero.

The conclusion uses the actual full abstract group center. Its datum consists
of a monoid homomorphism to complex units, an open kernel in the center's
subspace topology, norm-one values, and scalar action of each central element
on every vector. It uses the existing structure in
`Langlands.Representation.MatrixCoefficient.ModuloCenter` without introducing
another package. The central character is asserted to exist, without a
particular choice or an additional uniqueness clause.

## Internal provenance and intended derivation

This is an internal algebraic consequence of existing Library interfaces.
It does not purport to transcribe a separate original-source theorem.
`Langlands.admissibleSchur_centralCharacter` in
`Langlands.Representation.Smooth.Schur.Proof` already proves existence and
uniqueness of a locally constant complex-unit central character with actual
scalar action under irreducibility and admissibility. Its locally constant
kernel is open. The remaining norm-one conclusion is the direct consequence
of the published invariant-form definition in
`Langlands.Representation.Unitary.Basic`: for a nonzero vector, definiteness
makes its self-pairing nonzero, while scalar central action and invariance
identify this self-pairing with its product by the scalar's squared modulus.
Cancellation forces that modulus to be one. A proof successor must implement
this reasoning; no part of it is a premise of the proposition.

The statement is useful for the GL unitary Weyl exponent rigidity proof in
`Langlands.Representation.Classification.UnitaryWeylRigidityStatement`.
It does not assert that theorem's block-coordinate geometry, weighted real
exponent equalities, generic self-association consequence, or the host generic
relative Jacquet comparison.

This module records only the proposition. Its proposed algebraic derivation
and its use in exponent rigidity remain proof obligations.
