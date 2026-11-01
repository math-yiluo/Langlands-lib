# Spectral displacement detected by finite represented-domain covers

Let `K` be a complete ultrametric normed field and let
`A : PresentedAffinoidAlgebra K`. This module uses the existing
`Domain.FiniteCover`, actual bounded restrictions and constructed stabilizer
actions on the original domain algebras. It proves detection of spectral
bounds and section displacement by finite covers, with an explicit target
spectrum injectivity condition. The whole-spectrum and rational-chart
specializations prove that condition from their actual structural maps.

## Coverage of the target spectrum

A `Domain.FiniteCover V` supplies domains `c.obj i`, actual arrows
`c.map i : c.obj i ⟶ V` indexed by `Fin c.size`, and coverage of `V.locus`
inside `BanachSpectrum A`. It does not directly supply coverage of
`BanachSpectrum V.algebra`.

`Domain.FiniteCover.spectrum_jointly_surjective` assumes
`Function.Injective V.spectrumMap` and proves that every point of this target
quotient spectrum is the image of a point in a component quotient spectrum.
For a target point `x`, locus coverage chooses a component containing
`V.spectrumMap x`. The component's proved `spectrumToLocus_surjective` gives
a component point over that ambient point. The actual restriction's
`spectrumMap_over_base` equation and the target injectivity hypothesis
identify its image with `x`. No component injectivity is required.

`Domain.FiniteCover.spectralBound_iff` consequently identifies
`BanachSpectrum.SpectralBound b r` with the same uniform spectral bound on
every actual restriction `(c.map i).restriction b`. A spectral bound means
`x b ≤ r` for every point of the relevant Banach spectrum. Forward transport
uses the generic bounded ring-map lemma. For the converse, lift each target
point by the preceding joint-surjectivity result and evaluate its component
bound. The radius here is any real number; no positivity is needed.

`Domain.whole_spectrumMap_injective` proves injectivity for the whole domain
by extensionality of multiplicative seminorms, since its structural map is
the bounded identity. `spectralBound_whole_iff` uses it and the original
algebra `A`. `spectralBound_rational_iff` uses the published
`RationalChart.spectrumMap_injective`, proved from the original rational
spectrum-to-locus homeomorphism. Its section is an arbitrary element of the
actual rational quotient algebra; no lift to an ambient element is required.

## Restriction of section displacement

The remaining declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism`.
`mem_locusStabilizer_of_cover` proves that an ambient bounded automorphism
preserving each component locus setwise preserves their covered target
locus. One direction sends a point through its covering component. The other
applies the inverse automorphism inside a covering component and then uses
the group inverse law. This establishes equality of the image sets, rather
than merely one inclusion.

`restriction_sectionDisplacement` evaluates the published full bounded-map
square `stabilizerSectionMap_restriction` at an arbitrary target section `b`
and uses preservation of subtraction. Thus, when `g` preserves both source
and target,

```
restriction (targetAction(g)(b) - b)
  = sourceAction(g)(restriction b) - restriction b.
```

Both actions are the existing `stabilizerSectionAction`, constructed from
the full represented-domain universal property. They are not additional
input actions. The restriction remains the original bounded algebra map.

Write `H(V,b,r)` for `domainSpectralSubgroup V b r hr`, where
`hr : 0 ≤ r`; this notation is only explanatory. Membership includes target
locus stabilization and the uniform bound `r` on its actual section
displacement. For an injective target structural spectrum map,
`domainSpectralSubgroup_cover` proves

```
inf_i H(c.obj i, (c.map i).restriction b, r)
  = H(V,b,r) ∩ inf_i locusStabilizer(c.obj i).
```

In the forward direction, component test membership supplies every component
stabilizer. The union argument supplies the target stabilizer. The
restriction-displacement equation and `spectralBound_iff` then detect its
global displacement bound. In the reverse direction, transport the target
bound through each actual bounded restriction, rewrite with that equation,
and retain the supplied component stabilizer. The component stabilizers are
an essential part of the exact identity; target stabilization alone need not
preserve each member of its cover.

`domainSpectralSubgroup_cover_whole` and
`domainSpectralSubgroup_cover_rational` discharge target injectivity as above.
They impose no extra spectrum-injectivity assumption on their covers.

## Explicit finite refinements and their topology

`DomainSpectralTest.restrictToCover t c i` uses the actual component domain,
the restriction of `t.element`, and exactly the same positive radius and
positivity proof. `subgroup_restrictToCover` identifies its finite test
subgroup with the target test intersected with all component stabilizers.
`subgroup_restrictToCover_le` records refinement of that target test.
`isOpen_subgroup_restrictToCover` uses the existing openness theorem for
positive finite tests; this openness assertion needs no target injectivity.

`restrictDomainSpectralTestsToCovers tests covers` performs this construction
simultaneously for a family indexed by `ι : Type v`. Its explicit index is

```
Σ i : ι, Fin (covers i).size.
```

For finite `ι` this index is finite in its original independent universe.
`finiteDomainSpectralSubgroup_restrictToCovers` assumes injectivity of every
target structural spectrum map and proves that the localized subgroup is
the original finite test subgroup intersected with all stabilizers of all
cover components. The proof rewrites the infimum over the dependent sum as
iterated infima, applies the one-test identity, and distributes the infimum
over the two factors. The following `_le` theorem gives containment in the
original finite test subgroup.

`finiteDomainSpectralSubgroup_restrictToCovers_mem_nhds_one` and
`isOpen_finiteDomainSpectralSubgroup_restrictToCovers` prove that this explicit
subgroup is an identity neighborhood and open in `domainSpectralTopology A`.
They reuse the published arbitrary-finite-index theorems, without installing
a different topology on the automorphism group. These two conclusions need
only finiteness and the positive radii; the injectivity hypotheses are
required for the exact identity and refinement.

## Provenance and sources

This is an internal construction by Worker 56 from the published
`DomainTopology`, `DomainSpectralTests`, `DomainSpectralTopology`,
`DomainAutomorphism` and `RationalChartDomainComposition` APIs. It derives
joint target-spectrum surjectivity, bound detection and finite-test
refinement from actual cover witnesses and bounded maps. No standalone
original-source proposition is claimed for these internal lemmas.

Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
printed/PDF p.9 Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), and p.10
Fact 2.2.3(i) and Definition 2.2.7, fixes the represented-domain, rational
quotient, spectrum/locus and embedding conventions. The registered source is
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The rational specialization retains the published arbitrary positive-radius
quotient with explicit unit generation, a sufficient no-common-zero
condition whose converse is not asserted.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
manuscript (1996), section 1.1, printed/PDF pp.1–2, motivates finite
compact-domain, section and positive-tolerance tests for analytic
automorphisms. The registered source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
content SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The module uses uniform pointwise spectral bounds, without claiming an
equality between spectral and quotient norms or identifying its topology
with the manuscript's full analytic automorphism topology.

## Scope

The generic bound-detection and exact subgroup identities explicitly require
injectivity of the target structural spectrum map. Locus coverage alone
does not prove target quotient-spectrum coverage with the current `Domain`
API. Only the whole-domain and actual rational-chart cases discharge this
condition here. All declarations in this module use the complete-field
setting. They allow arbitrary positive polyradii, trivial valuations,
nilpotents, zero quotients, empty spectra and loci, empty covers of empty
targets, and empty finite test families. The last two give the expected
empty-intersection subgroup; no inhabitedness hypothesis is introduced.

The module assumes no algebra sheaf property, norm equality, common
operator-norm bound or full analytic atlas. It does not construct all compact
analytic domains or show cofinality of rational covers among them. General
analytic automorphism-topology comparison, compact/distinguished-domain
lifting, analytic etale/quasi-etale sites and the Harris tower remain
separate obligations.
