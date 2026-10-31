# Continuous finite-cover gluing inside actual rational charts

Author: Worker 56.

This module transports continuous maps on actual finite full-domain covers
through the constructed rational-chart locus homeomorphisms. The coefficient
field is complete and ultrametric. Affinoid algebras retain their chosen
finite positive-polyradius Tate-quotient presentations, and the continuous
target space is arbitrary: it need not be Hausdorff. Empty covers, zero
algebras, nilpotents and trivial valuations remain permitted.

## Extension of continuous families

`extendDomainLocusHomeomorph_symm_spectrumMap` states that applying the
rational spectrum map to the inverse locus comparison recovers the given
ambient point. It follows from the homeomorphism inverse law. The forward
comparison commutes with each actual domain inclusion by equality of the
underlying spectrum points. Its inverse commutes with those inclusions
because their spectrum images agree and the rational spectrum map is
injective.

`extendCoverFamily` precomposes every local continuous map with the inverse
component homeomorphism. `extendCoverFamilyInverse` precomposes with the
forward component map. To preserve overlap agreement under extension, equal
ambient points are lifted through the inverse comparisons and identified
by rational spectrum injectivity. In the other direction, equal inner
points have equal spectrum images, so the original ambient compatibility
applies. The two family inverse laws hold for all families, without a
compatibility hypothesis. They give `extendCoverFamilyEquiv` between the
subtypes of compatible families.

`extendCoverFamily_restrict` follows from inverse component naturality.
It identifies extension of the restrictions of a global map with restrictions
of that map composed with the inverse target homeomorphism. Consequently
`extendCoverFamilyEquiv_gluingEquiv` commutes with the existing explicit
gluing equivalences. The theorem `glue_extendCoverFamily` states that gluing
a transported compatible family equals the original glued map composed
with that same inverse target comparison. Its proof applies uniqueness of
gluing and the already proved restriction equation.

`extendCoverFamily_spectrumFamilyMap` identifies assembly before and after
extension on the unchanged finite disjoint union of actual component
quotient spectra. The component spectrum map after extension is the rational
spectrum map composed with the original component spectrum map. The inverse
locus homeomorphism therefore recovers the original component locus point,
which proves equality of the assembled continuous maps.

## Restriction of continuous families

For an ambient target `V` with an actual inclusion `f` into the chart,
`restrictDomainLocusHomeomorph_symm_spectrumMap` gives the same lifting
identity for its inverse-image locus. `restrictFiniteCover_locusMap` states
that the target and component comparisons commute with each actual
restricted cover inclusion. Its proof is equality of the underlying
spectrum points.

`restrictCoverFamily` precomposes with each forward component comparison
from the inverse-image locus to its original ambient locus.
`restrictCoverFamilyInverse` uses the inverse comparisons. Preservation of
compatibility applies the ambient compatibility to equal rational spectrum
images; inverse preservation uses the lifting identity and spectrum
injectivity. Both inverse laws again hold for arbitrary families.
`restrictCoverFamilyEquiv` bundles the resulting equivalence on compatible
families.

The restriction equation `restrictCoverFamily_restrict` follows from the
component inclusion diagram. It proves commutation with `gluingEquiv` and,
by gluing uniqueness, `glue_restrictCoverFamily`. The latter identifies the
new glued map with the original glued map composed with the forward target
comparison. `restrictCoverFamily_spectrumFamilyMap` states that assembly on
the unchanged actual component spectra is unchanged. Its proof uses the
commuting spectrum triangle of the composite component inclusion into the
rational chart. Both family transport operations commute with every
continuous map of target spaces.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.9, Definition 2.2.1 and Exercise 2.2.2(ii), supplies the full
affinoid-domain and positive-radius rational-quotient context. Printed/PDF
p.10, Fact 2.2.3(i) and Definition 2.2.7, supplies the represented-spectrum
and domain-embedding context. These original pages were read directly.
The actual charts retain explicit unit generation; no equivalence with
absence of common zeros is asserted.

The continuous-family comparisons and gluing equations are internally
derived from the Library's actual full domains, locus homeomorphisms and
quotient-topology gluing constructions. They are not separately numbered
assertions on those pages. The related bounded ambient equivalence
construction in `DomainCoverGluingTransport` supplies a pattern, but the
present rational structural map is not assumed to be an algebra equivalence.
The implemented gluing is the already constructed quotient lift for actual
finite covers; this module proves its compatibility with rational
localization. It does not assert algebra or module descent, Tate acyclicity,
rational-type flattening, analytic atlases or etale/equivariant sites.
