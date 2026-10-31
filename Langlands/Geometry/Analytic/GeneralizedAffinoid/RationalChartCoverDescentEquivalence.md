# Continuous descent along the actual rational cover equivalence

Author: Worker 56.

This module compares compatible continuous families along the actual inverse
of rational-chart finite-cover localization, including arbitrary ambient
covers. It identifies gluing over the restored inner target and proves
coherence with the actual cover-category unit and counit.

## Inputs and concrete comparison

The coefficient field is complete and ultrametric. Presented affinoid
algebras are actual quotients of finite positive-polyradius Tate algebras
by closed ideals, with their quotient norms and chosen presentations.
Full domains carry their representing algebra, bounded structural map,
closed locus, exact spectrum image and universal factorization against
every presented affinoid test. Rational charts retain explicit unit
generation and arbitrary positive radii.

For an inner full domain `U`, the existing
`finiteCoverLocalizationEquivalence d U` extends covers to
`d.extendDomain U`. Its actual inverse accepts any finite full-domain
cover of that ambient domain. It restricts every component along its
composite inclusion into the chart, then restores the target to `U`
through the constructed domain round-trip isomorphism. The input cover
need not have been constructed by extension.

`restrictExtendedCoverFamilyEquiv` reuses the previously constructed
restriction family equivalence. Restoring the target changes neither
component loci nor overlap agreement, so the compatible-family types
agree definitionally. Its forward map precomposes each ambient local
continuous map with the forward restricted-component locus homeomorphism.
Its inverse uses that homeomorphism's inverse. The two projection
lemmas expose these actual maps. Their inverse laws and overlap agreement
come from `RationalChartCoverGluing`, with no new output assumption.

The target `Y : Type v` is any topological space, in a universe independent
of the coefficient universe. No separation hypothesis is used.

## Naturality, assembly and gluing

`restrictExtendedCoverFamilyEquiv_pullback` proves the square for the
actual inverse functor on every supplied refinement. That functor retains
the chosen component index and the actual bounded restriction.
The square is the earlier restriction square because restoring the target
changes none of its component data. The inverse-refinement equation
applies injectivity of the transported pullback equivalence, uses this
square and cancels both inverse laws. The inverse refinement operation
is the existing one that glues the finer family and restricts to the
coarser cover.

`restrictExtendedCoverFamilyEquiv_spectrumFamilyMap` identifies assembly
on the same finite disjoint union of actual component quotient spectra.
Restriction retains these component algebras, and the earlier restriction
assembly theorem applies without a target change.

The global restriction equation uses
`extendDomainLocusHomeomorph U : U.locus ≃ₜ (d.extendDomain U).locus`.
Both component routes send an inner point to the same ambient spectrum
point. Extensionality proves the equation with the actual
`gluingEquiv` maps. The subsequent gluing equation applies the constructed
gluing equivalences and their inverse laws. Thus the glued restricted
family is the original quotient-glued map precomposed with the forward
target comparison, now on `U.locus`.

## Natural isomorphism and coherence

`restrictExtendedCoverFamilyNatIso d U Y` has source
`compatibleFamilyPresheaf (d.extendDomain U) Y` and target
`(finiteCoverLocalizationEquivalence d U).inverse.op` followed by
`compatibleFamilyPresheaf U Y`. Each component is the constructed
family equivalence converted to an isomorphism of types; the refinement
square proves naturality. The `hom_app` and `inv_app` equations expose
its two components. Its gluing equation compares the forward global
restriction components of the concrete quotient-gluing natural
isomorphisms.

`restrictExtendedCoverFamilyEquiv_extend_unit` says that restriction
after family extension equals pullback through the inverse unit of
`finiteCoverLocalizationEquivalence`. The proof uses the identity
component indices, the actual unit restrictions and the inverse law
of the component locus homeomorphism.
`extend_restrictExtendedCoverFamilyEquiv_counit` says that extension
after restriction of any ambient family equals pullback through the
actual counit. The proof uses the proved spectrum-lifting identity for
the inverse component locus homeomorphism. These equations identify the
composites through actual refinements of covers, rather than identifying
different cover objects by a type cast.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p.9, supply the full
affinoid-domain and positive-radius rational-quotient context.
Fact 2.2.3(i) and Definition 2.2.7, printed/PDF p.10, supply the
represented-spectrum and actual domain-embedding context. Explicit unit
generation remains in force, without an asserted equivalence with
absence of common zeros.

The inverse-functor family comparison, gluing equations and coherence are
internal consequences of the Library's actual domain localization,
cover-category equivalence and continuous quotient-gluing constructions.
They are not separately numbered assertions from these pages.
The component-family transport is reused from `RationalChartCoverGluing`
and its refinement naturality from `RationalChartCoverFamilyNaturality`;
this module adds the actual inverse cover functor, restored target and
unit/counit comparison.

Empty covers, empty loci, zero algebras, nilpotents and trivial valuations
remain permitted at the existing chosen-presentation scope. No algebra
or module descent, Tate acyclicity, rational-type flattening, analytic
atlases or etale/equivariant sites are asserted.
