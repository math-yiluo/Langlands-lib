# Finite-cover refinement categories inside actual rational charts

Author: Worker 56.

This module constructs a categorical equivalence between finite full-domain
covers of an inner domain over an actual rational quotient and covers of
its extension to the original affinoid base. Every refinement retains its
chosen component indices and actual bounded algebra restrictions.

## Inputs and actual refinement maps

The coefficient field is complete and ultrametric. The presented affinoid
algebras are actual finite positive-polyradius Tate algebras modulo closed
ideals, with their quotient norms. A full domain retains its actual
representing algebra, structural bounded map, locus and proved universal
representation. The imported cover localization constructs both extension
and restriction of finite full-domain covers using actual rational
quotients. It retains component algebras and bounded target restrictions
and proves coverage, rather than requiring a new coverage hypothesis.

The existing refinement category records, for every finer component, a
chosen coarser component and an actual domain restriction. Different index
choices remain different arrows. `extendCoverRefinement` retains the index
function and applies the actual domain extension functor to each arrow.
`restrictCoverRefinement` retains both the index function and bounded
restriction. Its new equation over the quotient follows by composing the
original refinement triangle with the supplied inclusion into the chart.
Projection lemmas expose the retained indices and bounded maps. Their
continuous maps between the unchanged disjoint unions of component spectra
are definitionally the original maps.

`extendFiniteCoverFunctor` and `restrictFiniteCoverFunctor` bundle these
constructions. Identity and composition follow from refinement
extensionality: once the index functions agree, uniqueness of actual
full-domain restrictions determines the component arrows.
Both functors preserve the canonical refinement to the concrete singleton
identity cover. The final spectrum equations combine the actual refinement
triangle with the previously constructed cover-locus homeomorphisms.

## Inverse and categorical equivalence

For an inner domain `U`, `restrictExtendedFiniteCover` accepts any cover of
`d.extendDomain U`. It restricts each component along its composite
inclusion into the rational chart. It then composes the target restriction
with the actual isomorphism from the restricted extended target to `U`.
The proved equality of the target loci supplies coverage. Thus the input
cover need not have been produced by extension. The finite indices and
actual component algebras are retained; composing with the target comparison
retains each original bounded restriction because that comparison uses
the identity bounded map.

`restrictExtendedFiniteCoverFunctor` acts on each refinement by the same
restriction construction. `finiteCoverLocalizationUnitIso` uses the
identity component index and identity bounded algebra maps in both
directions. Their structural equations are the original component
restriction equations over the inner base. For the ambient counit,
`finiteCoverLocalizationCounitIso` uses the actual domain round-trip
isomorphism on each component with its composite inclusion into the chart.
These isomorphisms also retain the component index and use identity bounded
maps on the component algebra.

The inverse laws, naturality and equivalence triangle reduce by refinement
extensionality to the identity index functions. The entry
`finiteCoverLocalizationEquivalence d U` bundles the extension functor and
constructed inverse as
`Domain.FiniteCover U ≌ Domain.FiniteCover (d.extendDomain U)`.
This is an equivalence of the actual chosen-index refinement categories,
including empty finite covers whenever they cover their target.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.9, Definition 2.2.1 and Exercise 2.2.2(ii), gives the full
affinoid-domain and arbitrary positive-radius rational-quotient context.
Printed/PDF p.10, Fact 2.2.3(i) and Definition 2.2.7, gives the represented
spectrum and actual domain-embedding context. These pages were read
directly. Explicit unit generation remains in the actual chart data; no
equivalence with absence of common zeros is asserted.

The refinement functors and equivalence are internal consequences of the
Library's actual domain localization, finite-cover transport and
chosen-index refinement category. The related bounded-base-equivalence
construction in `DomainCoverRefinementTransport` provides the categorical
pattern; the present inverse instead uses restriction along the rational
chart and does not require its structural map to be a bounded algebra
equivalence. These constructions are not separately numbered source
assertions. They retain the Library's chosen positive-polyradius
presentations, and permit zero algebras, nilpotents and trivial valuations.
They do not establish rational-type flattening, arbitrary morphism base
change, algebra-section descent, analytic atlases or etale/equivariant sites.
