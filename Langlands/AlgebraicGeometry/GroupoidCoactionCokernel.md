# Cokernel coactions and surjectivity of invariant maps

This is internal algebraic infrastructure derived from the published
`GroupoidCoaction` definition. It does not prove the Serre criterion.

For an equivariant map `f : M →ₗ[B] N`, `cokernelSemilinearMap` composes the
coaction on `N` with the tensor of the quotient map to `N / range f`.
Equivariance and the vanishing of the quotient map on `range f` show that
this semilinear map vanishes on the range, so `Submodule.liftQ` defines it
on the quotient. The resulting formula on quotient representatives is
`cokernelSemilinearMap_mkQ`.

`cokernel` applies `ofSurjective` to this formula: the diagonal and cocycle
identities descend along the surjective quotient map. Thus this construction
requires no flatness or equivalence-relation assumption, beyond the supplied
coactions. `cokernel_mkQ_isHom` records that the quotient map is equivariant.

For a `RingEtaleEquivalenceRelation`, `invariantsMap_surjective` assumes that
every coaction in the chosen module universe is acyclic. It constructs the
kernel coaction of an arbitrary equivariant surjection. The kernel subtype
is injective and equivariant, and its range is the kernel of the surjection.
Applying the published acyclicity predicate to this short exact sequence
lifts every invariant element. All three modules share the same universe,
as required by that predicate; the ring universe is independent.

These are derived constructions using the unchanged published coactions,
the preceding kernel and invariant-module helpers, and Mathlib's semilinear
quotient API. No geometric affineness or descent conclusion is assumed.
