# Finite direct sums of finite-dimensional representations

Worker 17 authored this construction module. It imports
`Langlands.Weil.Representation.Predicates` and pinned Mathlib.

For a family `A : ι → FiniteRepresentation K G` indexed by a finite type
`ι`, `directSum A` is the actual representation on Mathlib's direct sum
`⨁ i, A i`, with Mathlib's `Representation.directSum` action.
`directSum_representation` records that the action is the componentwise
map `DirectSum.lmap (fun i => (A i).representation g)`. Finite
dimensionality comes from Mathlib's instance for finite direct sums. The
index, group, coefficient and carrier universes are independent; the
carrier lives in `max uι uV`. The empty family and rank-zero summands are
allowed.

`directSumMap` is the componentwise sum of a family of linear
intertwiners; the intertwining identity follows from
`DirectSum.lmap_comp` and the componentwise identities. `directSumFunctor`
is a functor from the product category of `ι`-indexed families, with its
identity and composition laws proved through `DirectSum.lmap_id` and
`DirectSum.lmap_comp`. `directSumEquiv` turns a family of genuine
equivalences into an equivalence of direct sums via `Pi.isoMk`.
`rank_directSum` proves `rank (⨁ i, A i) = ∑ i, rank (A i)` from
Mathlib's `Module.finrank_directSum`.

`directSumClass` acts on a finite family of genuine isomorphism classes.
It uses Mathlib's `Quotient.finChoice` to pass from a family of classes to
a class of families, without choosing representatives, and descends the
direct sum through componentwise equivalences. `directSumClass_classOf`
computes it on representatives. This requires `[DecidableEq ι]`.

For a topological group `G` and a subgroup `I`,
`hasOpenInertiaKernel_directSum` proves the algebraic open-inertia
condition: the inertia kernel of the direct sum contains the finite
intersection of the component kernels, which is open.
`openInertiaDirectSum` and `openInertiaDirectSumClass` give actual
open-inertia objects and genuine classes. No usual-topology continuity,
irreducibility or semisimplicity preservation is asserted.

## Source correspondence

Henniart, *Une caractérisation de la correspondance de Langlands locale
pour GL(n)* (2002), §2.1, printed page 593 (PDF page 7), uses direct sums
`σ₁ ⊕ σ₂` of representations, and §2.2 on the same page describes every
representation of `W'_F` through the class of `⨁_{i∈I} σ_i` for a finite
index set `I`. Tate, *Number theoretic background*, Corvallis Part II, §2,
printed page 9 (PDF page 18), works with the set `M(G)` of isomorphism
classes of finite-dimensional representations; the class operation here
is the finite direct sum on such classes. Source IDs
`tate-1979-number-theoretic-background`
(SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`)
and `henniart-2002-characterization`
(SHA-256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`).
The finite-family construction on Mathlib's `⨁`, its intrinsic functor and
quotient obligations, and the open-kernel certificate are derived and
proved here; no decomposition theorem is asserted.
