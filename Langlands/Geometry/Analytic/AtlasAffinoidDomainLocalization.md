# Full affinoid-domain localization at original atlas chart containments

Authors: Worker 36 and Worker 56.

`AtlasAffinoidDomainLocalization.lean` constructs restriction of full affinoid
domains along an original atlas chart containment and an equivalence with the
ordinary category of domains over its relative chart domain. Both directions
retain the represented algebras and the actual bounded maps.

The namespace is `Langlands.Analytic.IndexedAffinoidAtlas`. Let `K` be a complete
ultrametric normed field, `X` a topological space, and `a` an
`IndexedAffinoidAtlas K X`. The field/algebra, ambient-space and index universes
are independently `u`, `v` and `w`. Put `Aᵢ = a.algebra i` and `cᵢ = a.chart i`.
Fix an original chart containment `h : range cᵢ ⊆ range cⱼ`, and write
`r = a.restriction i j h : Aⱼ → Aᵢ` and
`D = a.restrictionDomain i j h`. Its spectrum map is the actual comap along `r`,
and its locus is `cⱼ ⁻¹' range cᵢ`.

## Restriction and its full universal property

For `V : Domain K Aⱼ` and an actual domain inclusion `f : V ⟶ D`, set
`q = f.restriction : Aᵢ → V.algebra`. The inclusion stores the bounded-map
equation `q.comp r = V.baseMap`.

`represents_domainRestriction` proves that `q` fully represents the locus
`D.spectrumMap ⁻¹' V.locus` over `Aᵢ`. Its proof has three parts.

- Closedness follows by continuous inverse image from the closed locus of `V`.
- The inclusion equation gives the commuting spectrum triangle
  `D.spectrumMap (M(q) y) = V.spectrumMap y`. This proves that the image of
  `M(q)` lies in the asserted inverse image. Conversely, the exact spectrum
  image of `V` gives a lift of any point in that inverse image. The embedding
  `a.isEmbedding_restriction i j h`, derived from the original chart square,
  supplies injectivity and identifies that lift over `Aᵢ`.
- Given any actual presented affinoid test algebra `R` and bounded map
  `φ : Aᵢ → R` with spectrum image in the inverse-image locus, the composite
  `φ.comp r` has image in `V.locus`. The full representation of `V` supplies
  a unique bounded factor `θ : V.algebra → R` over `Aⱼ`.
  `a.restriction_hom_ext i j h R` then recovers
  `θ.comp q = φ` from its composite equation with `r`. This cancellation
  is uniqueness in the original chart domain's full affinoid-test universal
  property. Any competing factor over `Aᵢ` is a competing factor over `Aⱼ`,
  giving uniqueness.

`restrictDomain i j h V f` stores exactly `V.algebra`, the structural map `q`,
and this inverse-image locus, with the proved representation property.
The algebra, base-map and locus lemmas expose these defining formulas.
`restrictDomain_baseMap_comp` records its composite equation with `r`.

`restrictDomainOfSubset` takes instead a locus containment
`V.locus ⊆ D.locus`. The existing full representation of `D` constructs
the actual bounded inclusion by `Domain.inclusionOfSubset`, after which the
same restriction construction applies. Its algebra and locus formulas remain
the same.

All algebras and tests are the actual finite positive-polyradius Tate quotients
in `PresentedAffinoidAlgebra K`. The construction permits nonstrict and
nonreduced algebras, empty spectra and trivially valued complete fields.

## The equivalence and its actual arrows

Mathlib's `Over D` is formed in the existing category `Domain K Aⱼ`.
An object consists of a full domain over `Aⱼ` and an actual inclusion into `D`;
an arrow is a commuting triangle of actual domain inclusions.

`extendDomainOverFunctor i j h` lifts the extension from
`AtlasAffinoidDomainExtension` to `Over D` using `extendDomainInclusion`.
Its map on an arrow retains the original bounded restriction, and the triangle
is the original base equation. `restrictDomainFunctor i j h` retains the
bounded restriction of the ambient arrow. Applying
`congrArg Domain.Inclusion.restriction` to the triangle equation supplies
the required base equation over `Aᵢ`.

`restrictExtendDomainIso` constructs the inner round-trip comparison, and
`extendRestrictDomainIso` constructs the ambient round-trip comparison.
Both directions of each comparison are identity bounded maps on the unchanged
represented algebra. The ambient base equations are `f.comp_baseMap` and its
reverse. The four comparison restriction lemmas expose these identity maps.
`Domain.locus_eq_of_iso` then proves the exact locus equalities
`restrict_extendDomain_locus` and `extend_restrictDomain_locus`.

`domainLocalizationEquivalence i j h` constructs

`Domain K Aᵢ ≌ Over D`.

Its functor and inverse are the two functors just described. The unit is the
reverse of the inner round-trip comparison. The counit lifts the ambient
round-trip comparison to `Over D`. Naturality, inverse laws and the triangle
equation are proved by extensionality of actual bounded restrictions and the
identity maps. No equivalence or output factorization is assumed.

Forgetting the over-category inclusion recovers `extendDomainFunctor`
definitionally. Composing `restrictDomainFunctor` with `Domain.toAffinoidSpace`
or `Domain.toTopologicalSpace` definitionally agrees with first forgetting the
inclusion and then realizing the unchanged ambient domain algebra. These
equalities concern the actual represented algebras, bounded maps and spectra.

## Provenance and scope

This is a derived original-atlas construction. Its implementation substantially
adapts Worker 56's published
`Langlands/Geometry/Analytic/GeneralizedAffinoid/RationalChartDomainLocalization.lean`
and its proof pattern. Here the original chart restriction's
`restriction_hom_ext` replaces rational-quotient bounded-map cancellation,
and the embedding proved from the original chart square replaces rational
spectrum injectivity. The remaining categorical construction uses the
algebra-preserving extension along original chart containments.

The full domain convention is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), Definition 2.2.1, printed/PDF p.9. Fact 2.2.3(i) and
Definition 2.2.7, p.10, give the spectrum-identification and domain-embedding
context. Registered source `berkovich-2009-trieste-analytic-spaces`, SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The equivalence here is an internal consequence of the actual representation,
embedding and bounded-map uniqueness properties already available for these
original charts.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Lemma 1.2.5 and Proposition 1.2.6, printed pp.17–18 / PDF pp.14–15, provide
the broader atlas-extension context. Registered source
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Those results also treat a new domain lying in a different original chart
without containment of its chosen chart, using finite coverings and Tate
acyclicity.

The present construction requires containment of the entire original chart
`i` in the original chart `j`. It constructs localization of their full-domain
categories at that relative chart domain. The additional cross-chart
extension, extended atlas net, unrestricted strong composition, localization
of the analytic-space category, structure sheaves and etale or equivariant
sites remain separate constructions.
