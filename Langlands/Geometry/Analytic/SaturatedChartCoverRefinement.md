# Original-chart refinements of full-domain covers

Work over any complete ultrametric normed field, with independent universes for
the field, ambient topological space and original atlas index. The input is an
actual `IndexedAffinoidAtlas` satisfying `HasAllLocalDomains`. The preceding
construction proves this property for its actual `saturatedAtlas`; it is not
an assumed existence or gluing output in that application.

For every full domain `U` in an original chart `i`, `domainChartIndex` chooses an
original chart whose range is exactly `chart i '' U.locus`. This chart is
contained in `i`. `chartDomain` uses that original chart's presented algebra
and the original bounded restriction into `i`, with no replacement of their
norms or quotient presentations. Injectivity of `chart i` proves literal
equality of `chartDomain.locus` and `U.locus` inside the spectrum of chart `i`.

`chartDomainIso` then applies the existing full-domain comparison construction.
Its two arrows contain actual bounded algebra maps over the algebra of `i`,
and their inverse identities follow from full-test uniqueness in the domain
category. The two displayed structural equations retain these actual maps.
No equality of algebra maps is deduced from equality of spectrum point maps.

For any finite full-domain cover `c`, `chartCover c` keeps its size and finite
index. Each component is the constructed original-chart presentation of the
corresponding component of `c`. Its arrow to the covered domain is the inverse
comparison followed by the original arrow. Literal component-locus equality
transfers coverage. `chartCover_map_restriction` gives the exact contravariant
bounded-map formula. The two componentwise comparisons give refinements in
both directions, and `chartCoverIso` is their actual isomorphism in the cover
refinement category. The comparison followed by the transported arrow recovers
the original domain arrow. `chartCover_ambient_coverage` identifies the entire
union of the chosen chart ranges with the covered ambient image.

This is an internal construction from the actual original atlas restrictions,
the proved closure property, and the full-domain universal properties. It
introduces no additional literature attribution. It treats all full domains
and all finite covers, including empty covers, zero quotients, arbitrary closed
ideals and finite positive polyradii. No directedness, greatest chart,
nontrivial valuation, reducedness or nonempty spectrum is required.

These refinements supply actual original source charts for subsequent strong
morphism gluing on the constructed saturated atlases. This unit does not
construct general strong composition, extend arbitrary original strong-map data
to all local domains, or construct analytic or equivariant etale sites.
