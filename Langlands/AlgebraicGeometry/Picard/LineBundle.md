# Locally free sheaves of rank one on a scheme

`IsLocallyFreeRankOne M` says that every point of a scheme `X` has an open
neighborhood `U` on which the actual restriction `M.restrict U.ι` is isomorphic
to `SheafOfModules.unit U.toScheme.ringCatSheaf`. This is the local freeness
condition of rank one in Stacks Project, Definition 17.14.1(3), with the
singleton direct sum written as the structure sheaf itself.

`LineBundle X` is the full subcategory of `X.Modules` satisfying this predicate.
Thus a line bundle in this file is a sheaf, and its morphisms are module-sheaf
morphisms. `LineBundle.forget` forgets the property. `LineBundle.trivial` uses
the structure sheaf of `X`; its local triviality is supplied by Mathlib's
`Scheme.Modules.restrictUnitIso` on the whole open subset. No tensor product
or group structure is assumed or constructed in this file.

The helper `IsLocallyFreeRankOne.of_iso` composes the inverse restricted
isomorphism with the given local trivialization. It supplies `LineBundle.ofIso`
and `LineBundle.ofIsoIso`. `LineBundle.sections` evaluates the underlying
abelian presheaf on the whole space, so it is the actual abelian group of global
sections. `trivializingOpen`, `mem_trivializingOpen`, and `localTrivialization`
choose and expose a neighborhood and its trivialization from the local property.

All definitions use `Scheme.{u}` and the pinned Mathlib's `X.Modules` universe
conventions. No smallness of the collection of isomorphism classes is asserted.

## Scope and subsequent comparison

Stacks Project Definition 17.25.1 defines an invertible module by tensoring
being an equivalence. Lemma 17.25.4 identifies it with local freeness of rank
one when the structure sheaf has local stalks, as schemes do. This file only
constructs the local rank-one side. It does not prove or assume that comparison;
a precise statement must use the forthcoming genuine scheme-module tensor
construction. The eventual scheme Picard construction and tensor inverse remain
separate work.

## Source and implementation provenance

Registered source: `stacks-local-freeness-invertibility-sections-2026-10-21`,
content SHA-256 `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
The retained files are `01C5.html`, Section 17.14, Definition 17.14.1(3), and
`01CR.html`, Section 17.25, Definition 17.25.1 and Lemma 17.25.4. Original links:
[local freeness](https://stacks.math.columbia.edu/tag/01C5) and
[invertible modules](https://stacks.math.columbia.edu/tag/01CR).

The full-subcategory packaging, transport definitions, and chosen trivializations
are internal implementations of this local definition using Mathlib's restriction
functor and isomorphisms. They do not add mathematical hypotheses or assert an
unproved result from the source.
