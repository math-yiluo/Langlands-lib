# Relative representations along full affinoid-domain inclusions

Author: Worker 36.

This module constructs a full relative affinoid-domain representation from an
existing inclusion `f : V ⟶ U` of full domains over the same presented algebra
`A`. It also constructs a fully faithful functor
`Domain.relativeFunctor U : Over U ⥤ Domain K U.algebra`.
All declarations belong to `Langlands.Analytic.PresentedAffinoidAlgebra`, with
the domain constructions in its `Domain` namespace.

The coefficient field `K : Type u` is any complete ultrametric normed field.
All algebras are the existing actual finite positive-polyradius closed Tate
quotient presentations. The representation predicate quantifies over every
such test algebra. Trivial valuations, zero and nonreduced quotients, empty
coordinate tuples and empty spectra are allowed. No injectivity assumption
is used to construct the relative domain or functor.

## Cancellation and relative representation

The shared `Represents.hom_ext`, imported from `DomainCancellation`, proves
that precomposition with a representing structural
map `i : A → B` cancels among bounded maps `f,g : B → R`, for every actual
presented-affinoid test algebra `R`. The common composite has spectral image
in the represented locus because the spectrum comap factors through `M(B)`.
The uniqueness clause of the full representation property then identifies
the two maps.

`Represents.of_comp` takes full representations for `i : A → B` and
`j.comp i : A → C` and proves that `j : B → C` represents its own actual
spectral image. That image is closed because the source spectrum is compact,
the target spectrum is Hausdorff, and bounded comap is continuous. For a test
map `φ : B → R` whose spectrum image lies in this image, its composite with
`i` has image in the locus represented by `j.comp i`. The latter universal
property produces a bounded `ψ : C → R`. Cancellation along `i` proves
`ψ.comp j = φ`; uniqueness for the composite proves uniqueness for `j`.
These arguments concern equality of whole bounded homomorphisms.

For `f : V ⟶ U`, `Domain.represents_relative` applies that result to
`U.baseMap` and `f.restriction`; the arrow's base equation identifies the
composite with `V.baseMap`. `Domain.relative U V f` consequently has exactly
`V.algebra`, structural map `f.restriction`, and locus
`Set.range f.spectrumMap` inside `M(U.algebra)`. The algebra, base-map and locus
projection lemmas are definitional equalities, and `relative_baseMap_comp`
retains the original equation over `A`.

`image_relative_locus` proves that this new locus maps onto exactly `V.locus`
in `M(A)`, using the existing exact-image clause for `V` and the inclusion's
spectrum naturality. `relative_locus_subset_preimage` proves containment in
`U.spectrumMap ⁻¹' V.locus`. The separate theorem
`relative_locus_eq_preimage_of_injective` proves equality with that inverse
image if the particular map `U.spectrumMap` is injective: lift an ambient
point through `V` and use that injectivity to identify its image with the
specified point in `M(U.algebra)`. No general injectivity theorem is asserted.

## Actual maps and the fully faithful functor

An object of `Over U` consists of an ambient domain and its specified bounded
inclusion into `U`. `relativeFunctor` sends it to the relative representation
just constructed. It sends a commuting triangle to the same bounded
restriction. Applying the restriction projection to the triangle equality
proves its equation over `U.algebra`. Identity and composition are preserved
as equalities of actual domain arrows.

`fullyFaithfulRelativeFunctor` constructs an inverse on each hom set. A bounded
relative inclusion already commutes with the structural maps from
`U.algebra`. Composing that equation with `U.baseMap` produces the ambient
base equation; the same relative equation gives the whole commuting
triangle. The two inverse laws follow by extensionality of domain arrows and
over-category arrows. The resulting `Full` and `Faithful` instances are
provided. The two `relativeFunctor_comp_to...` theorems state literal equality
with the forgetful ambient functor after realization by actual affinoid spaces
or by their topological spectra.

`relativeInclusion` retains the actual bounded restriction of a nested
ambient inclusion. `relative_relative` proves literal equality of repeated
and direct relative representations, including their algebra, base map and
spectral-image locus. This module does not prove essential surjectivity of
the functor, an equivalence of domain categories, unrestricted composition of
domain representations, or full inverse-image localization without the stated
injectivity input. It constructs no structure sheaf or analytic site.

## Provenance

These are derived consequences of the published full representation property,
rather than verbatim source theorems. The original is V. G. Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p. 8, gives the space direction dual to bounded
affinoid algebra maps. Definition 2.2.1, printed/PDF p. 9, gives the closed-image
and unique-factorization clauses used here. The Lean proof derives relative
representation by the two universal properties and cancellation; it does not
invoke the general spectrum identification in Fact 2.2.3(i). Compactness and
Hausdorffness come from the published actual bounded-spectrum construction.
The category packaging and the exact retained-algebra identities are internal
consequences of those constructions.
