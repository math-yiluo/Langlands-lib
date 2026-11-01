# Rational-domain atlases on actual affinoid spectra

Author: Worker 36.

For a complete ultrametric normed field `K : Type u` and an actual finite
positive-polyradius quotient `A : PresentedAffinoidAlgebra K`, this module
constructs `RationalSpectrumAtlas.atlas A` on the actual bounded multiplicative
seminorm spectrum `BanachSpectrum A`. The result is an `IndexedAffinoidAtlas`
with its point and index types both in universe `u`.

## Charts and their literal domains

The published `RationalChart K A` retains finitely many series representatives
for a denominator and numerators, arbitrary positive real radii, and a proof
that their coefficient classes generate the unit ideal of `A`. Its algebra
is the actual closed rational quotient, and its structural map is bounded.
The published spectrum homeomorphism identifies its spectrum with its rational
inequality locus in `BanachSpectrum A`.

`Index K A` consists of literal subsets of that spectrum which are loci of
such rational presentations. Existence of a presentation is a proposition,
not additional index data. Therefore two indices with the same subset are
equal, even if their initial rational presentations differ. `ofChart` supplies
the index of any given rational presentation. `presentation` chooses one actual
presentation for each subset; `locus_presentation` proves its locus equality.
`representativeIso` uses the published full representation theorem to construct
an isomorphism from any given rational chart to the representative of its locus.
Its arrows contain actual bounded maps over `A`; no equality of quotient ideals
or presentations is claimed.

The atlas chart is the representative's actual structural spectrum map.
`range_chart` identifies its range with the indexed subset. Its injectivity
follows from the published homeomorphism to that locus; compactness of its
spectrum and Hausdorffness of the base give a closed embedding, hence the
required embedding. Subtype extensionality proves `chartDomain_injective`.
`family_eq_range_locus` and `atlas_chartFamily` identify the chart family
exactly with all the above rational loci.

## The net and local separation

`Index.whole` uses the published zero-numerator, denominator-one rational
presentation. Its locus is the whole spectrum. Thus the chart family is a
quasinet, with the whole spectrum as a one-member neighborhood witness.
`Index.inter` uses the published all-products rational presentation on two
chosen representatives. Its locus is their exact intersection. On each pairwise
intersection, this intersection chart becomes the whole subspace. The same
one-member witness proves the required quasinet on that induced subspace.
This proves `isNet_family`. The actual base spectrum is Hausdorff, so its
whole subspace supplies the local Hausdorff condition.

The construction allows empty spectra, empty rational loci and zero arities.
No point or nonempty chart is chosen in the net proof.

## Full bounded restrictions and coherence

For an inclusion of chart ranges, `restriction` uses the published
`RationalChart.restrictionOfSubset` on their chosen representatives. This
constructs the entire bounded map from the containing quotient to the contained
quotient by the containing chart's full affinoid-test representation.
`restriction_comp_baseMap` states its equation over `A`.
`restriction_chart` is the corresponding structural spectrum equation.

`restriction_universal` proves the relative full factorization property required
by the atlas. Given a bounded map from the containing quotient to any actual
presented affinoid test algebra `R`, compose with its structural map from `A`.
The assumed spectrum-image containment places this composite in the smaller
base locus. The smaller chart's full representation gives a unique bounded
factor from its quotient to `R`. The containing chart's proved uniqueness
of bounded maps over `A` identifies its composite with the original test map.
Any competing relative factor has the same composite over `A`, so uniqueness
in the smaller representation proves equality of the factors.

`restriction_id` and `restriction_comp` use the published uniqueness of
bounded rational-chart arrows over `A`. They prove equality of complete
bounded homomorphisms, not only of their induced spectrum maps. Nilpotents
and nonreduced quotient algebras are retained.

`atlas` packages precisely these constructions and proved obligations.
`atlas_ofChart_range` shows that every rational locus is an actual chart,
and `atlas_whole_range` identifies a greatest chart with the whole spectrum.

## Original sources and scope

The original atlas definition is Vladimir Berkovich, *Étale cohomology for
non-Archimedean analytic spaces*, 1993, registered as
`berkovich-1993-etale-cohomology`, PDF SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13, require a
net of compact domains on a locally Hausdorff space, actual affinoid algebras,
and bounded restrictions identifying contained charts with affinoid domains.
These passages were read directly.

For the rational charts, the original is Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures, 2009, registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p.9, give the
affinoid-domain universal property, positive-radius rational quotients and
closure under intersections. Fact 2.2.3(i), p.10, gives the spectrum/locus
identification. These pages were read directly.

This atlas is an internal construction from the published actual quotient,
full representation, whole-chart and intersection results. The proof route
above derives its relative universal property rather than assuming an atlas
or analytic-space output. The explicit unit-ideal generation condition and
chosen finite positive-polyradius presentations of all test algebras remain
the scope of the imported results. Radii need not lie in a value group, the
valuation may be trivial, and no reducedness assumption is imposed.

The module supplies genuine smaller rational charts on an affinoid spectrum.
It does not claim that every affinoid domain is rational, a saturated or maximal
atlas, general extension of an arbitrary atlas, a structure sheaf, finite
analytic gluing, unrestricted strong-map composition, or an étale or equivariant
site. In particular it does not prove Berkovich 1993 Proposition 1.2.6.
