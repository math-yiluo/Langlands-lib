# Finite full-domain covers inside an actual rational chart

Author: Worker 56.

This module transports finite full-domain covers between an actual rational
quotient and its original base. It uses the full domain extension and
restriction constructions, retaining their actual positive-polyradius
quotient algebras and bounded maps over a complete ultrametric normed field.
The constructions permit zero algebras, nilpotents, trivial valuations and
empty finite families.

## Locus comparisons and covering

`extendDomainLocusHomeomorph d U` identifies an inner domain's locus with
its spectrum image in the original base. It restricts the actual rational
spectrum embedding, whose injectivity was proved from the rational quotient
spectrum homeomorphism. Its underlying map is exactly `d.spectrumMap`.

For an ambient domain `V` with an actual inclusion `f : V ⟶ d.toDomain`,
`restrictDomainLocusHomeomorph d V f` identifies its inverse-image locus
over the quotient with `V.locus`. The inclusion gives containment in the
rational spectrum map's range, so restriction of that embedding gives a
homeomorphism. The two application lemmas expose the actual spectrum map.

`familyCovers_extendDomain_iff` proves preservation and reflection of
pointwise coverage for any indexed family of inner full domains, with an
independent index universe. Forward reflection uses injectivity to identify
the inner point with a point of a covering component; preservation takes
spectrum images. `familyCovers_restrictDomain_iff` gives the corresponding
equivalence for ambient components equipped with inclusions into `V`.
Restriction uses the preimage membership directly. Reflection lifts a point
of `V.locus` through the constructed locus homeomorphism and applies coverage
there. Thus neither equivalence assumes a finite nonempty index set.

## Actual finite cover constructions

`extendFiniteCover d c` retains `c.size`, extends each actual component
domain, and applies `extendDomainFunctor` to its actual target restriction.
The first covering equivalence supplies coverage. Each component algebra
and bounded restriction is unchanged definitionally.

`restrictFiniteCover d f c` retains `c.size` and restricts each component
along `c.map i ≫ f`. Its target restriction is precisely the original
`(c.map i).restriction`; the base equation over the quotient is the
definition of the composite inclusion. The second covering equivalence
supplies coverage. Projection lemmas expose the retained indices, objects,
algebras and bounded maps. Both constructions preserve the concrete singleton
identity cover.

The two component-map equations compare the actual maps from the unchanged
component quotient spectra to the target locus, using the constructed locus
homeomorphisms. Extension's equation is pointwise composition of bounded
maps. Restriction's equation is the commuting spectrum triangle of the
actual composite inclusion. The two total-map equations assemble these
component equations over the same finite disjoint union of actual spectra.
Consequently the finite spectrum-cover diagrams, and the existing quotient
topology results applicable to them, are available in both ambient bases.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.9, Definition 2.2.1 and Exercise 2.2.2(ii), supplies the
full affinoid-domain and positive-radius rational-quotient context.
Printed/PDF p.10, Fact 2.2.3(i) and Definition 2.2.7, supplies the
representing-spectrum and actual domain-embedding context. These pages
were read directly. The actual rational charts retain explicit unit
generation; no equivalence with absence of common zeros is asserted here.

The locus comparisons, covering equivalences, finite-cover constructions
and spectrum diagrams are internal consequences of the actual Library
domain constructions and elementary topology. They are not separately
numbered assertions from the source. The algebras and full representation
tests remain the Library's chosen finite positive-polyradius presentations.
This module does not prove rational-presentation flattening, arbitrary
domain base change, Tate acyclicity, algebra or module gluing, an analytic
atlas, or an etale/equivariant site.
