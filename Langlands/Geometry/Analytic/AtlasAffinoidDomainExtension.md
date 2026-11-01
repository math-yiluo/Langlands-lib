# Full affinoid domains along original atlas chart containments

`AtlasAffinoidDomainExtension.lean` constructs extension of full affinoid-domain
representations along every containment between two original charts of an
`IndexedAffinoidAtlas`. It retains the actual represented algebra and every bounded
restriction map, and proves compatibility with self-containment and nested
containments.

The namespace is `Langlands.Analytic.IndexedAffinoidAtlas`. Let `K` be a complete
ultrametric normed field, `X` a topological space, and `a` an indexed affinoid atlas
on `X`. Write `Aᵢ = a.algebra i` and `cᵢ = a.chart i`. The algebra universes, ambient
space universe and index universe are independently `u`, `v`, and `w`. Every
algebra here is the actual finite positive-polyradius Tate quotient stored in a
`PresentedAffinoidAlgebra K`.

## Original chart topology

For an original containment `h : range cᵢ ⊆ range cⱼ`, put
`rᵢⱼ = a.restriction i j h`. This is the actual bounded algebra map `Aⱼ → Aᵢ`
in the original atlas. Its spectrum map satisfies the original chart square

`cⱼ ∘ M(rᵢⱼ) = cᵢ`.

The published `isEmbedding_restriction` from `StrongQuasiIsoComposition` cancels
the embedding `cⱼ` from this square. This module reuses that declaration. Thus the
spectrum map is an embedding, including its topology; its injectivity is derived
from the original chart embeddings. The published full-domain universal property
alone is not used to infer injectivity.

`restrictionSpectrumHomeomorph` combines this embedding with the published exact
range equation to give

`M(Aᵢ) ≃ₜ (cⱼ ⁻¹' range cᵢ)`.

Its displayed forward map is exactly spectrum comap along `rᵢⱼ`.

## Extension of arbitrary full domains

Let `U : Domain K Aᵢ`. `extendDomain i j h U` is the full domain over `Aⱼ` with:

- algebra exactly `U.algebra`;
- structural map exactly `U.baseMap.comp rᵢⱼ`;
- locus exactly `M(rᵢⱼ) '' U.locus`.

Its full representation property is proved by the published generic
`Represents.comp_of_injective`, applied to the original restriction's full
representation, `U.represents`, and the injectivity just derived.
That composition proof first factors an arbitrary bounded test map through
`Aᵢ`; spectrum injectivity makes the factor land in `U.locus`, after which the
full representation of `U` supplies the unique second factor. Compactness of
the inner closed locus supplies closedness of its image in the Hausdorff
affinoid spectrum.

Consequently all tests remain arbitrary presented affinoid algebras with finite
positive polyradii. There is no strictness, reducedness, nonempty-spectrum, or
nontrivial-valuation hypothesis.

`extendDomain_locus_subset` places the result inside the original relative chart
domain. `chart_image_extendDomain_locus` proves the exact ambient subset equation

`cⱼ '' (extendDomain i j h U).locus = cᵢ '' U.locus`.

`extendDomainInclusion` constructs its actual inclusion into
`a.restrictionDomain i j h`; its bounded restriction is exactly `U.baseMap`.

## Bounded maps and containment compatibility

`extendDomainFunctor i j h` maps full domains over `Aᵢ` to full domains over
`Aⱼ`. Its map on each arrow is the original bounded restriction, and its base
equation follows by associativity. `fullyFaithfulExtendDomain` constructs an
inverse on every Hom set. The published `restriction_hom_ext` derives the
required base equation over `Aᵢ` from the equation over `Aⱼ`, using uniqueness in
the original restriction's full affinoid-test universal property. Equality of
maps is proved as equality of bounded algebra homomorphisms.

The composites with `Domain.toAffinoidSpace` and `Domain.toTopologicalSpace` are
definitionally the original functors on domains over `Aᵢ`. These functors realize
each unchanged represented algebra and its actual spectrum.

`extendDomainSelfIso` identifies extension along any self-containment with the
identity functor. `extendDomainCompIso` identifies extension along `i ⊆ j ⊆ k`
with direct extension along `i ⊆ k`. The components in both directions use
bounded identity maps on `U.algebra`. Their base equations use, respectively,
the original atlas's `restriction_id` and `restriction_comp`; naturality follows
because all extension functors retain the original bounded restrictions.
`extendDomain_self_locus` and `extendDomain_comp_locus` give the corresponding
exact locus equalities through these constructed isomorphisms.

## Provenance and scope

This is a derived construction from the published original-atlas and full-domain
interfaces. It specializes transitivity of full domain representations to an
original atlas chart inclusion, where the needed spectrum embedding has been
proved from the chart square.

The original domain convention is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), Definition 2.2.1, printed/PDF p.9: a closed locus with
the exact spectrum image and unique factorization of every affinoid map into
that locus. Registered source `berkovich-2009-trieste-analytic-spaces`, SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Lemma 1.2.5 and Proposition 1.2.6, printed p.17 through the beginning of p.18 /
PDF pp.14–15, give the broader context of extending an atlas by affinoid domains.
Registered source `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original argument also handles a new domain that is contained in another
original chart without containment of its chosen containing chart; that step
uses intersections, finite coverings and Tate acyclicity.

The present module assumes an original chart containment `i ⊆ j` and constructs
extension along it. It does not implement the additional gluing needed for
Lemma 1.2.5 in that broader situation, or the entire extended net and atlas in
Proposition 1.2.6. Relative restriction, unrestricted strong composition,
analytic-space localization, sheaves and sites remain separate constructions.
