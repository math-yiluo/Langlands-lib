# Smooth representability of Hom from a split torus

`Langlands.GroupScheme.HomScheme.SmoothSplitSourceRepresentabilityStatement.{u}`
states that for every scheme `S` in universe `u`, every split torus `H/S`,
and every smooth affine group scheme `G/S`, there is a scheme `M/S` and
an actual universal group-scheme homomorphism `H_M ⟶ G_M`, with `M → S`
smooth.

Universality is the interface condition `IsUniversal i`:
for every test scheme `T/S`, evaluation gives a bijection between actual
maps `T ⟶ M` over `S` and actual homomorphisms `H_T ⟶ G_T`.
The evaluation uses the actual pullback-composition and equality-of-base-map
comparisons defined in `HomScheme.Universal`. It therefore identifies the
actual relative Hom presheaf with the functor of points of `M`.

The base is arbitrary, including nonreduced and nonnoetherian schemes.
The definition `IsSplitTorus` requires a finite index type and an actual
group-scheme isomorphism with the corresponding product of copies of
the multiplicative group. No connectedness condition is placed on `G`
or its fibres. The conclusion does not require `M` to be affine or
quasi-compact.

## Source and specialization

The original result is SGA 3, Exposé XI, Corollary 4.2, in the
Gille–Polo provisional recomposition of 5 December 2008:
`Expo11.pdf`, PDF pages 20–21, recomposed printed pages 104–105,
original page numbers 157–158. It asserts representability, smoothness,
and separatedness of the group-homomorphism functor when `G` is smooth
and affine and `H` is of multiplicative type and finite type.
The registered source is
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, folder fingerprint
`dd37c114bfb569a0d39c1cce727a0d87a8d40abf545d13e0b1a2d886d03b7498`,
retained at
`literature/Grothendieck - SGA 3 Exposes XI, XII and XIV (Gille-Polo provisional recomposition, December 2008)`.
No source-specific erratum is present in the supplied errata notes.

This proposition specializes the source to a split torus and retains
only representability and smoothness. The finite split source is smooth,
so the first paragraph of the source proof applies: graphs identify Hom
with an open subfunctor of the functor of multiplicative-type subgroups
of `H ×_S G`, using Exposé XI, Theorem 4.1, and Exposé IX, Corollary 2.9.
These are proof inputs to establish or replace; this file does not
assume or prove them.

## Status and use

This file defines a proposition and supplies no proof of representability.
It is a generic prerequisite for pointed lifting. A prescribed
residue-field homomorphism gives an actual point of `M` by universality;
a separately proved pointed smooth-local-section theorem can retain
that point on an etale neighbourhood. Closed-immersion conditions
require a further argument and are not asserted here.
