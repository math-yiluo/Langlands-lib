# Finite-cover refinement localization at a specified embedded domain

Author: Worker 36, adapting Worker 56's published
`DomainCoverRefinementTransport` construction.

For a particular full represented domain `d : Domain K A` and a proof
`hd : Function.Injective d.spectrumMap`, this module constructs an
equivalence between the finite-cover refinement categories of an inner
domain `U : Domain K d.algebra` and its ambient extension
`d.extendOfInjective hd U`. Both functors retain the finite component
indices, actual component algebras and bounded component restrictions.
The morphisms retain their chosen index functions.

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover`.
The coefficient assumptions are exactly `NormedField K`,
`IsUltrametricDist K` and `CompleteSpace K`. The existing presented
algebras are finite positive-polyradius Tate algebras modulo closed
ideals, with their quotient norms. A full domain retains its actual
structural bounded map, closed spectral locus, exact image and unique
factorization against every presented affinoid test.

## Refinement transport and functors

The imported `DomainEmbeddedCoverLocalization` constructs finite covers
by extension and relative passage, retaining the component algebras and
bounded restrictions. `DomainCoverRefinement` supplies the category of
finite covers. A morphism `Refinement e c` chooses an index of `c` for
every index of `e`, together with an actual domain arrow from that finer
component to the selected coarser component.

`Refinement.extendOfInjective` retains `r.index` and applies the actual
domain extension functor to each `r.map i`.
`Refinement.relativeOfInjective d hd f` treats covers of an ambient
domain `V` supplied with its actual arrow `f : V ⟶ d`. It views each
component arrow as an arrow in the category over `d`, then applies the
imported `d.relativeFunctor`. The commuting triangles follow from the
proved uniqueness of actual domain arrows. Each resulting bounded
restriction is definitionally the original restriction.

`extendFunctorOfInjective` and `relativeFunctorOfInjective` bundle these
constructions. `Refinement.ext` proves the functor laws by equality of
the retained index functions; the remaining actual component arrows are
determined by full affinoid-test uniqueness. Distinct index choices are
therefore preserved. The spectrum-map equations show that extension and
relative passage leave the entire continuous refinement map unchanged:
the finite disjoint unions contain the same actual quotient spectra and
use the same bounded restrictions.

## Inverse and equivalence

For an arbitrary cover `c` of `d.extendOfInjective hd U`,
`extensionInverseObjOfInjective` retains its finite index set and makes
each component relative to `d` along the actual composite
`c.map i ≫ d.extendOfInjectiveInclusion hd U`.
Its arrow to `U` is the relative inclusion followed by
`d.relativeExtendOfInjectiveIso hd U`. The latter restores the exact
original target after the relative-extension round trip. Coverage
follows from the relative finite-cover construction and the proved
equality of that round-trip target locus with `U.locus`.
The construction accepts every cover of the extended target; it does
not assume that the cover was previously obtained by extension.

`extensionInverseOfInjective` applies the relative functor to each
chosen refinement arrow. Its index function, bounded restrictions and
continuous map on the actual disjoint unions of spectra are unchanged.
The target round-trip isomorphism has identity bounded restriction, so
it does not change the original target restrictions either.

`extensionUnitIsoOfInjective` and `extensionCounitIsoOfInjective` use
identity index functions in both directions. For the unit, the component
arrows store identity bounded maps on the retained algebras; their base
equations are exactly the original component inclusions' bounded base
equations. For the counit, the component arrows are the imported actual
`extendRelativeOfInjectiveIso` maps, also with identity bounded
restrictions. The inverse laws, naturality and triangle identity follow
by refinement extensionality from the identity index functions.

The entry declaration `localizationEquivalenceOfInjective` bundles
these concrete functors and natural isomorphisms as

```text
FiniteCover U ≌ FiniteCover (d.extendOfInjective hd U).
```

The imported forward cover construction preserves the singleton
identity cover. `extendOfInjective_toSingleton` additionally identifies
the extension of its canonical refinement arrow with the canonical
arrow of the extended cover, retaining its selected singleton index.

## Actual spectrum-cover diagrams

`extensionInverseObjOfInjective_totalMap` compares the inverse cover's
total map with the original cover's total map through
`d.extendOfInjectiveLocusHomeomorph hd U`. The source is the same finite
disjoint union of actual component quotient spectra. Evaluation at
each point reduces the equality to the spectrum triangle of the
original composite inclusion into `d`.

`extendOfInjective_spectrumMap_over_target` combines the extended
refinement triangle with the imported forward cover triangle: the
extended coarser cover's total map after the unchanged refinement map
is the original finer cover's total map followed by the actual
extension-locus homeomorphism.
`relativeOfInjective_spectrumMap_over_target` gives the corresponding
relative triangle. Composing the relative coarser total map and the
unchanged refinement map with the relative-locus homeomorphism recovers
the original finer total map. Its proof combines the relative
refinement triangle with the imported relative cover triangle.
These statements retain the actual quotient spectra; no component
spectrum is replaced by its locus.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p. 8, gives the contravariant bounded-map
category. Definition 2.2.1, printed/PDF p. 9, gives full affinoid-test
domain representation. Definition 2.2.7, printed/PDF p. 10, gives the
affinoid-domain embedding category.

This finite-cover category equivalence and its spectrum diagrams are
internal consequences of the domain localization and finite-cover
constructions. They adapt the concrete inverse, unit and counit method
of `DomainCoverRefinementTransport` to a specified embedded domain.
They are not separate numbered assertions from Berkovich. Only the
particular outer map `d.spectrumMap` is assumed injective; neither `U`
nor any cover component has an injectivity hypothesis. The input has
actual examples, including whole-spectrum and rational domains, whose
structural injectivity is already proved in the imported development.

Trivial valuations, arbitrary finite positive polyradii, zero
quotients, nilpotents, empty spectra and empty covers are permitted.
The module does not prove general full-domain spectrum injectivity,
arbitrary-domain base change, algebra-section descent, Tate acyclicity,
unrestricted analytic atlas saturation, or an etale/equivariant site.
