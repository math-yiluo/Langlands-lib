# Pure dimension of affine schemes and their component quotient rings

This is an internal algebraic comparison for the componentwise pure-dimension
condition used in Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2). Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad does not introduce this separate ring predicate or these comparison maps.
They express the existing scheme predicate in the pinned Mathlib algebra API.

All declarations are in
`Langlands.AlgebraicGeometry.SchemeFiberGeometry`, in arbitrary universe `u`.
`HasPureRingDimension A d` requires, for each actual minimal prime ideal p of A,
that the quotient ring A/p have Krull dimension d. The natural number d is cast
into `WithBot ℕ∞`, just as in `HasPureDimension`. There is no Noetherian,
finite-type, field or nontriviality hypothesis. In particular the zero ring
satisfies this condition vacuously, since it has no prime ideals.

`quotientSpectrumZeroLocusHomeomorph I` constructs the actual homeomorphism
between the prime spectrum of A/I and the zero locus V(I) in the prime spectrum
of A, with its subspace topology. It uses the closed embedding induced by the
surjective quotient homomorphism and the identification of its range with V(I).
`topologicalKrullDim_zeroLocus` then transports topological Krull dimension
along this homeomorphism and applies Mathlib's equality between the
topological dimension of a prime spectrum and the ring's Krull dimension.

`hasPureDimension_spec_iff` proves that `HasPureDimension (Spec A) d` is
exactly `HasPureRingDimension A d`. In one direction, the zero locus of each
minimal prime is an irreducible component of the actual prime spectrum. In
the other, Mathlib identifies every irreducible component as the zero locus
of a minimal prime. The preceding dimension equality supplies the same
componentwise number in both directions. This compares every component,
rather than just the dimension of the whole space. Finally,
`hasPureDimension_iff_globalSections` applies the scheme isomorphism from an
affine scheme to the spectrum of its actual global-section ring, followed by
the preceding equivalence.

This definition and its intrinsic comparisons provide the algebraic interface
for further field-extension arguments. They do not prove field-extension
invariance, constructibility of fibre loci or filtered descent. No
nonaffine version is inferred from an arbitrary affine cover here.
