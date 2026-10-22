# Normal-subgroup invariants

Worker 17 authored this generic construction module for task
`503968de-16f8-4f63-ba13-b5e167e11dce`. It imports the published
`Langlands.Weil.Representation.Basic` foundation from Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.

For a finite-dimensional representation on its actual carrier,
`invariantSubspace A I` is Mathlib's submodule of vectors fixed by every
element of the specified subgroup `I`. When `I` is normal, `invariants I A`
uses Mathlib's `Representation.toInvariants` to give that subspace the
ambient group action. Finite dimensionality follows from the subspace
instance. `invariantsInclusion` is the inclusion intertwiner.
The `invariants_isTrivial` instance exposes the trivial restricted subgroup
action through the finite-representation wrapper.

`invariantsMap` restricts an actual linear intertwiner to the two fixed
subspaces. Equivariance proves that fixed vectors map to fixed vectors.
The identity and composition equations in `invariantsFunctor` are proved
on the underlying linear maps. `invariantsEquiv` transports actual
isomorphisms through this functor, and `invariantsClass` descends the
construction to the genuine isomorphism-class quotient.

The field, group and carrier universes are independent; the map constructor
also permits different source and target carrier universes. No topology,
finiteness of the subgroup, averaging, or characteristic-zero assumption is
needed. Normality is explicit and is used only to obtain the ambient group
action.

This is a general algebraic construction underlying the invariant space in
Tate, *Number theoretic background*, Corvallis Part II, printed page 20,
§4.1.6 (`tate-1979-number-theoretic-background`, retained Part II PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`).
It does not define an Euler factor. The implementation reuses pinned Mathlib
`RepresentationTheory/Invariants.lean`, in particular `invariants` and
`toInvariants`, at commit `5ed2965256430c3649e86755f9576b54eca72435`.
