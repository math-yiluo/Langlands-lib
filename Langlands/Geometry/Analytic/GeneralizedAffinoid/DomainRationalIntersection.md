# Intersecting a full affinoid domain with an actual rational chart

Author: Worker 36.

Over any complete ultrametric normed field `K`, this module constructs the
intersection of a full represented domain `U : Domain K A` and an ambient
positive-radius rational chart `d : RationalChart K A`. The underlying
algebra is the actual rational quotient after coefficient pullback to
`U.algebra`. The construction requires no injectivity of `U.spectrumMap`.
The existing finite positive-polyradius quotient presentations allow
trivial valuations, nilpotents, zero quotients and empty spectra.

## Composition over an entire inverse image

`Represents.comp_preimage` takes an actual bounded map `i : A → B`
representing `U`, an actual bounded map `j : B → C` representing the
entire inverse image of an ambient set `V` under the spectrum map of `i`,
and a proof that `V` is closed. It proves that `j.comp i` represents
`U ∩ V` against every presented affinoid test algebra.

The intersection is closed. Its equality with the composite spectral
image follows in one direction from the two given image containments.
For the reverse inclusion, lift a point of `U ∩ V` through the spectral
image of `i`. This lift lies in the specified entire inverse image of
`V`, so the spectral image of `j` supplies the second lift. Composition
then recovers the original point.

For a test map with image in the intersection, first use the full
representation of `U` to factor through `B`. The bounded factorization
equation implies that every spectrum point of the factor maps into `V`,
so this factor has image in the entire inverse image represented by
`j`. The second full representation gives the required map from `C`.
Uniqueness follows by applying the first universal property to the
composite of a competing map with `j`, then the second universal
property to the competing map itself. There is no pointwise cancellation
of the spectrum map of `i`.

## Actual intersection and bounded projections

`Domain.rationalInter U d` applies this lemma to the proved representation
of `RationalChart.pullback U.baseMap d`. The published `pullback_locus`
equation identifies its locus with the required entire inverse image.
The constructed intersection has:

- Algebra `(RationalChart.pullback U.baseMap d).algebra`.
- Structural bounded map
  `(RationalChart.pullback U.baseMap d).baseMap.comp U.baseMap`.
- Locus `U.locus ∩ d.locus`.

Projection lemmas expose these fields definitionally.
`rationalInterLeft` has bounded restriction equal to the pulled chart's
structural map. `rationalInterRight` has bounded restriction
`RationalChart.pullbackMap U.baseMap d`; its equation over `A` is the
published whole bounded-map equation `pullbackMap_comp_baseMap`.

`rationalInterLift` constructs an actual bounded inclusion from any full
domain equipped with inclusions into both factors. Containment in the
intersection follows from the two supplied maps, and the full
representation property constructs the bounded restriction.
The two projection equations use uniqueness of actual domain arrows.

`rationalInterPullbackCone f g` uses these concrete projections for any
two inclusions of `U` and `d.toDomain` into a common full domain.
`rationalInterPullbackConeIsLimit` supplies a lift for every cone by
`rationalInterLift`; the actual hom spaces are subsingletons by the full
affinoid-test universal property, giving the cone and uniqueness equations.

## The actual spectrum pullback

`rationalInterSpectrumCone U d` specializes the published rational
coefficient-change spectrum cone to the actual map `U.baseMap`.
Its point is definitionally the spectrum of the constructed intersection
algebra. Its two projections are definitionally the continuous spectrum
maps of `rationalInterLeft` and `rationalInterRight`; the three projection
lemmas expose these identities. `rationalInterSpectrumConeIsLimit`
reuses the proved rational spectrum pullback limit. Thus this spectrum
square is a topological pullback even without injectivity for the full
domain's structural spectrum map.

## Original source and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1, printed/PDF p. 9, gives the closed-image and full
affinoid-test unique-factorization property. Exercise 2.2.2(ii), p. 9,
gives the positive-radius rational quotient and its inequalities.
Exercise 2.2.2(iii), p. 9, asserts intersection stability of affinoid
domains. Definition 2.2.7, printed/PDF p. 10, supplies the affinoid-domain
embedding context.

This is an internal derived construction of the case in which one
ambient domain has a rational presentation. The general preimage
composition lemma is proved directly from the full universal property;
the rational pullback provides its needed quotient and representation.
The categorical and topological limit packaging is derived here from
the implemented maps and the published rational coefficient-change
construction. The module does not construct the intersection of two
arbitrary full domains, prove general full-domain spectrum injectivity
or Gerritzen–Grauert rational coverage, or supply a saturated atlas,
Tate acyclicity or an etale/equivariant site.
