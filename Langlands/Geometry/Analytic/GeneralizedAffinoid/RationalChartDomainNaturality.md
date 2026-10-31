# Full-domain localization through nested actual rational charts

Author: Worker 56.

This module transports a full represented domain through an actual inclusion of
rational charts over a fixed presented affinoid algebra. It constructs the
transport functor, proves full faithfulness, and makes both directions of the
existing domain-localization equivalences natural in the chart inclusion.
Identity and composition comparisons retain the actual representing algebra
and have explicit coherence equations.

The coefficient field `K` is complete and ultrametric. The ambient algebra `A`
and every domain algebra are the Library's actual finite positive-polyradius
Tate quotients by closed ideals. The charts `d` and `e` have chosen rational
data with explicit unit generation. An arrow `f : d ⟶ e` stores an actual
bounded map `e.algebra → d.algebra` with its equation over `A`; it is an
inclusion in the space direction. `U : Domain K d.algebra` supplies a closed
locus, an actual representing algebra and bounded structural map, exact spectrum
image, and unique factorization against every presented affinoid test.

## Construction and its actual spectrum

`nestedDomainInclusion f U` composes the existing ambient inclusion
`d.extendDomain U ⟶ d.toDomain` with the actual domain inclusion induced by
`f`. Its bounded restriction is exactly `U.baseMap.comp f.restriction`.
`nestedDomain f U` applies `e.restrictDomain` to this ambient domain and
inclusion. The preceding domain composition and localization results prove
its full representation property. No additional representation witness or
desired transported object is an input.

The resulting domain retains `U.algebra` exactly and has structural bounded
map `U.baseMap.comp f.restriction`. Its construction first describes the locus
as `e.spectrumMap ⁻¹' (d.spectrumMap '' U.locus)`.
`nestedDomain_locus` proves that this is exactly
`f.spectrumMap '' U.locus`. To lift a point in the inverse image, use its
preimage in `U.locus`, the over-base spectrum equation for `f`, and injectivity
of `e.spectrumMap`. The reverse inclusion follows from the same over-base
equation. `nestedDomain_spectrumMap` identifies the structural spectrum map
with the composite of `U.spectrumMap` and the spectrum map of the actual
bounded restriction.

`nestedDomainLocusHomeomorph f U` restricts the already proved closed
spectrum embedding of `f` to `U.locus`, then uses the exact locus equality.
Its forward map is the actual `f.spectrumMap`. The pointwise
`nestedDomain_spectrumToLocus` equation says that this homeomorphism takes
the original structural image of every spectrum point to its transported
structural image. The domain's representing algebra is unchanged throughout.

## Functor and natural locus diagram

`nestedDomainFunctor f` retains each inner arrow's bounded restriction.
Associativity of bounded-map composition and the original inner base equation
prove the transported base equation. Its identity and composition laws follow
by extensionality of the stored bounded maps.

`fullyFaithfulNestedDomain f` constructs an inverse on each hom-set by keeping
the given bounded map. To recover its equation over `d.algebra` from the
transported equation over `e.algebra`, first precompose with `e.baseMap`.
The equation stored by `f` turns this into an equation over `A`.
The published rational-quotient uniqueness theorem for `d` then recovers the
equation over `d.algebra`. In Lean this uses pointwise equality and
`congrArg` on the actual bounded maps. Both inverse laws are extensional
equalities of the unchanged maps. The preimage restriction lemma exposes this
map, and the construction supplies the functor's `Full` and `Faithful`
instances.

`nestedDomainLocusHomeomorph_naturality` proves that every actual inner domain
inclusion commutes with the locus homeomorphisms: both paths have the same
underlying point `f.spectrumMap x`. `nestedDomainLocusNatIso` bundles the
homeomorphisms into an isomorphism from the original domain-locus diagram to
the transported domain-locus diagram in `TopCat`.
`nestedDomainLocusNatIso_spectrumToLocus` bundles the pointwise structural
spectrum equation into an equality of natural transformations. The
affinoid-space and spectrum realization functors themselves are preserved
definitionally, as the final two realization lemmas state.

## Naturality of the localization equivalences

The existing `domainLocalizationEquivalence d` identifies full domains over
`d.algebra` with actual ambient domains equipped with an inclusion into
`d.toDomain`. Write `F_d` for its extension functor and `G_d` for its
restriction functor. The actual ambient arrow induced by `f` gives Mathlib's
postcomposition functor `Over.map` from `Over d.toDomain` to
`Over e.toDomain`.

`extendNestedDomainIso f U` compares the ambient extension of the transported
domain with `d.extendDomain U`. It is the existing ambient round-trip
comparison for `e`, applied to `nestedDomainInclusion f U`. Both bounded
restrictions are identities on `U.algebra`, as its projection lemmas show.
`extendNestedDomainNatIso` proves naturality after forgetting the inclusion
into the chart.

`nestedLocalizationNatIso f` retains that inclusion and constructs

```text
nestedDomainFunctor f ⋙ F_e ≅ F_d ⋙ Over.map (toDomainFunctor.map f).
```

Its components lift the same identity-map comparisons to the ordinary over
category. Their triangle equations and naturality follow by extensionality
of the actual bounded restrictions.

`nestedRestrictDomainIso f V` compares transporting the restriction of
`V : Over d.toDomain` with restricting `V.left` directly along its inclusion
into `e.toDomain`. Both algebras are `V.left.algebra`, both base maps over
`e.algebra` are the composite of `V.hom.restriction` with `f.restriction`,
and the two comparison maps are actual identities. Its projection lemmas
expose these maps. `nestedRestrictionNatIso f` gives the inverse square

```text
G_d ⋙ nestedDomainFunctor f ≅ Over.map (toDomainFunctor.map f) ⋙ G_e.
```

Thus both squares concern the constructed localization functors and the
actual chart arrow.

## Identity and composition coherence

`nestedDomainIdIso d U` compares transport along the identity chart inclusion
with `U`. `nestedDomainCompIso f g U` compares successive transport along
`f : d ⟶ e` and `g : e ⟶ h` with transport along `f ≫ g`.
Every forward and inverse bounded restriction in these comparisons is the
identity on `U.algebra`; the four projection lemmas expose this fact.
Extensionality proves their inverse laws and naturality, giving
`nestedDomainIdNatIso` and `nestedDomainCompNatIso`.

The two identity-comparison equations identify composition with an identity
with the appropriate transported or direct identity comparison.
`nestedDomainCompIso_assoc` compares the two actual paths from three
successive transports to transport along the triple composite.
`extendNestedDomainIso_comp` compares the two paths to the original ambient
extension. Their proofs use extensionality and equality of the explicit
identity bounded maps.

`nestedDomainLocusHomeomorph_id` states the identity equation on locus points,
including the actual domain comparison.
`nestedDomainLocusHomeomorph_comp` says that successive locus homeomorphisms,
followed by the actual composition comparison, equal the locus homeomorphism
for `f ≫ g`. These proofs use subtype extensionality and equality of the
underlying multiplicative seminorms on every algebra element.

## Source and construction scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.9, Definition 2.2.1, gives the full affinoid-domain universal
property, and Exercise 2.2.2(ii) gives arbitrary positive-radius rational
quotients. Printed/PDF p.10, Fact 2.2.3(i), gives the representing-spectrum
identification context, and Definition 2.2.7 defines actual affinoid-domain
embeddings. These original pages were read directly. Explicit unit generation
remains a hypothesis on the chosen rational charts; this module does not
identify it with the source's absence-of-common-zeros condition.

The nested full-domain construction, natural localization squares, and
coherence comparisons are internal consequences of the published Library's
actual domain composition and localization constructions, rational-quotient
uniqueness, and spectrum embeddings. Their implemented proofs are described
above. The output is a full represented domain and is not claimed to carry
a single rational presentation over `e.algebra`. In particular, this module
does not implement the rational-flattening assertion of Exercise 2.2.4.
It also does not assert a presentation theorem for arbitrary abstract
affinoids, arbitrary domain base change, algebra or module descent, analytic
atlases, etale sites, or equivariant sites. Empty loci, zero algebras,
nilpotents, arbitrary positive radii, and trivial valuations remain permitted.
