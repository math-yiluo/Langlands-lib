# Finite full-domain covers along a specified embedded domain

Author: Worker 36. Adapted from Worker 56's published
`RationalChartDomainCoverLocalization` construction.

This module transports actual finite full-domain covers along a particular
full represented domain `d : Domain K A` with a supplied proof
`hd : Function.Injective d.spectrumMap`. All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain`. The coefficient field
is any complete ultrametric normed field, and algebras are the existing
finite positive-polyradius closed Tate quotient presentations. Inner
domains have no injectivity hypothesis. Zero quotients, nilpotents,
trivial valuations, empty spectra and empty finite covers are permitted.

## Relative loci and covering families

`relativeLocusHomeomorphOfInjective d hd V f` identifies the actual relative
locus of an ambient inclusion `f : V ⟶ d` with `V.locus`. The imported
relative construction uses the same algebra as `V`, the bounded map
`f.restriction`, and its actual spectral range. Its conditional
inverse-image equality identifies that range with
`d.spectrumMap ⁻¹' V.locus`. The specified continuous injective map is a
closed embedding by compactness and Hausdorffness. Restricting it to that
inverse image gives the homeomorphism, since `f.subset` puts `V.locus`
in its range. The application lemma exposes exactly `d.spectrumMap`.

`familyCovers_extendOfInjective_iff` proves preservation and reflection of
pointwise covering by any indexed family of inner domains. Forward
reflection uses `hd` to identify the two inner points with the same image;
preservation takes images of covering points. The index type has its own
universe and may be empty.

`familyCovers_relativeOfInjective_iff` treats ambient components equipped
with their actual inclusions into `V`. To recover an ambient cover, lift
each target-locus point through the relative-locus homeomorphism, apply
relative coverage, and use containment in the corresponding inverse image.
In the other direction apply ambient coverage at the image point and use
the conditional inverse-image equality for the chosen component. The same
specified `hd` suffices for every component.

## Finite covers and their spectrum diagrams

`extendFiniteCoverOfInjective d hd c` retains the finite index and extends
each component by `extendOfInjective`. Its arrows are the images of the
original arrows under `extendOfInjectiveFunctor`. The first covering
equivalence supplies the covering proof. Each actual component algebra
and each bounded target restriction is unchanged definitionally.

`relativeFiniteCoverOfInjective d hd f c` retains the finite index and
passes each component to its relative domain along `c.map i ≫ f`. Its
target restriction is exactly `(c.map i).restriction`; the base equation
is the definition of that composite inclusion. The second covering
equivalence supplies coverage. Projection lemmas expose the finite
index, component domain, component algebra and bounded map. Both
constructions preserve the singleton identity cover literally.

The component-map equations compare the actual maps from the unchanged
component quotient spectra to the two target loci. Extension commutes
with `extendOfInjectiveLocusHomeomorph` by evaluating the composite bounded
maps at each seminorm. Relative passage commutes with
`relativeLocusHomeomorphOfInjective` by the original composite inclusion's
spectrum triangle. The total-map equations assemble these identities
over the same finite disjoint union of actual component spectra.
Thus the imported finite-cover quotient-topology results apply on either
side to these concrete diagrams.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p. 8, gives the contravariant bounded-map
category. Definition 2.2.1, printed/PDF p. 9, gives the full
closed-image and unique-factorization property. Definition 2.2.7,
printed/PDF p. 10, gives the affinoid-domain embedding context.

The homeomorphism, covering equivalences and actual spectrum diagrams
are internal consequences of these domain constructions and elementary
topology, generalizing the published rational-chart construction to any
particular full domain with the specified injectivity proof. They are
not separate numbered assertions in Berkovich. This module does not
prove injectivity for arbitrary full domains, arbitrary domain base
change, rational-presentation flattening, Tate acyclicity, algebra or
module gluing, unrestricted atlas saturation, or an etale/equivariant site.
