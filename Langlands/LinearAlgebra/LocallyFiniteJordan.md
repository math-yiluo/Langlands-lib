# Compatible Jordan components of locally finite endomorphisms

This module constructs compatible linear Jordan components for a locally finite
endomorphism over a perfect field. The field and the source and target vector
spaces have independent arbitrary universes. The field may have any
characteristic, the ambient vector spaces may have arbitrary dimension, and
zero vector spaces are included.

## Finite invariant subspaces and local finiteness

`FiniteInvariantSubspace f` consists of a submodule of the ambient vector space,
a proof that it is finite dimensional, and a proof that `f` preserves it.
Its `restrict` endomorphism is the actual restriction of `f`.
Its `sup` is the sum of two such submodules, which is again finite dimensional
and invariant. These definitions require only a field.

`IsLocallyFinite f` is the proposition that every vector belongs to one of
these finite invariant subspaces. It imposes no uniform bound on their
dimensions. It is an explicit premise of the global constructions.

## Compatible components

For a perfect field, `FiniteInvariantSubspace.semisimpleMap` is the canonical
finite-dimensional semisimple component of the restricted endomorphism,
followed by inclusion in the ambient space. The finite Jordan naturality
theorem shows that these maps agree under inclusions of finite invariant
subspaces.

`locallyFiniteJordanValue` initially chooses a finite invariant subspace for
each vector. Comparing any two choices inside their sum proves that the value
agrees with `semisimpleMap` on every finite invariant subspace. Using a common
sum for two vectors proves additivity; using the subspace of a single vector
proves compatibility with scalar multiplication.
`locallyFiniteSemisimplePart` bundles these values as a linear endomorphism.
Its evaluation theorem identifies it with the finite canonical part on
every finite invariant subspace of the original endomorphism.

## Naturality and the complementary component

`locallyFiniteSemisimplePart_intertwines_finite` treats every linear
intertwiner from a finite-dimensional space into a locally finite
endomorphism. The image of that map is a finite invariant subspace, and
finite-dimensional Jordan naturality proves the identity there. Restricting
the source to a finite invariant subspace through each vector then proves
`locallyFiniteSemisimplePart_intertwines` for every linear intertwiner between
two locally finite endomorphisms. Neither intertwiner must be injective or
surjective.

`locallyFiniteNilpotentPart` is the difference of the original endomorphism
and its global semisimple component. On each finite invariant subspace it
intertwines with the finite nilpotent part, so a power kills every vector.
The exponent may depend on the vector; global nilpotence is not asserted.
Naturality with the original endomorphism proves commutation, and subtraction
then proves that the two components commute.

## Provenance and scope

All content is derived from the finite-dimensional Jordan components and
intertwiner theorems in `JordanChevalleyFunctoriality`, together with elementary
finite-submodule and image constructions from Mathlib. No external structural
result is assumed. The name of the global semisimple component records its
compatibility with the finite semisimple parts; this module does not prove
a separate global `Module.End.IsSemisimple` predicate. It does not construct
components for endomorphisms lacking the local-finiteness premise, prove a
derivation property, or prove Cartan generation.
