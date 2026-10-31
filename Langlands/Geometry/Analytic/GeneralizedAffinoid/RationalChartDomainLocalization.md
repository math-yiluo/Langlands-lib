# Localizing full domains at an actual rational chart

Author: Worker 56.

This module constructs both directions of an equivalence between full domains
over an actual rational quotient and full ambient domains equipped with an
actual bounded inclusion into that rational chart. The coefficient field is
complete and ultrametric. Algebras and tests are the Library's finite
positive-polyradius Tate quotients, with zero algebras and nilpotents allowed.

## The inverse domain construction

For `d : RationalChart K A`, `V : Domain K A` and an actual inclusion
`f : V ⟶ d.toDomain`, `restrictDomain d V f` retains exactly `V.algebra`.
Its structural bounded map is exactly `f.restriction : d.algebra → V.algebra`,
and its locus is `d.spectrumMap ⁻¹' V.locus`. The stored inclusion equation
gives `f.restriction.comp d.baseMap = V.baseMap`.

`represents_restriction` proves its full representation property directly.
Closedness is preserved by the continuous rational spectrum map. For the
exact spectrum image, the inclusion equation gives the commuting spectrum
triangle. The ambient domain's exact range gives a lift, and injectivity of
the rational spectrum map identifies that lift over the quotient. Every test
map over `d.algebra` whose image lies in the inverse-image locus can first be
composed with `d.baseMap`. The full ambient representation then gives a
unique bounded factor. The rational quotient's published bounded-map
uniqueness recovers the equation over `d.algebra` from its equation over `A`.
Any competing factor satisfies the same equation over `A`, proving uniqueness.
No representation or injectivity witness is added to the inputs.

`restrictDomainOfSubset d V h` takes only `h : V.locus ⊆ d.locus` beyond the
two existing objects. The proved full representation of the rational chart
constructs its actual inclusion by `Domain.inclusionOfSubset`; the preceding
construction then applies. Its algebra and inverse-image locus are unchanged.

## The category equivalence and its actual maps

`Over d.toDomain` is Mathlib's ordinary over category of `Domain K A`.
Its objects are full ambient domains with actual bounded inclusions into the
rational chart, and its arrows are commuting triangles of actual domain
inclusions. It is not an assumed analytic-space category.

`extendDomainOverFunctor d` lifts the actual extension construction from
`RationalChartDomainComposition` to this over category, retaining the bounded
inclusion `extendDomainInclusion`. On arrows it retains the original bounded
restriction; its commuting triangle is exactly the inner base equation.
`restrictDomainFunctor d` retains the ambient arrow's bounded restriction.
The over-category triangle supplies its base equation over `d.algebra`.

`restrictExtendDomainIso` and `extendRestrictDomainIso` construct the two
round-trip comparisons using identity bounded maps on the unchanged quotient
algebras in both directions. For the ambient comparison, the equations over
`A` are the original inclusion equation and its reverse. The four restriction
lemmas expose these identity maps. The represented loci therefore also agree
in both round trips, as stated by the two locus lemmas.

`domainLocalizationEquivalence d` uses these functors and comparisons to
give `Domain K d.algebra ≌ Over d.toDomain`. The unit is the reverse of the
inner round-trip comparison, and the counit lifts the ambient round-trip
comparison to the over category. Naturality, both inverse equations and the
triangle equation follow by extensionality of actual restrictions and their
identity maps. The proof does not assume uniqueness of arbitrary category
morphisms. Forgetting the over-category inclusion recovers the preceding
extension functor definitionally. Restriction preserves the affinoid and
bounded-seminorm spectrum realization functors definitionally.

## Source and construction scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1, printed/PDF p.9, is the full affinoid-domain universal
property; Exercise 2.2.2(ii) constructs rational quotients at arbitrary
positive radii. Fact 2.2.3(i), p.10, supplies the representing-spectrum
identification context, and Definition 2.2.7 describes affinoid-domain
embeddings. These pages were read directly. Explicit unit generation is
retained for the actual rational charts, without asserting its equivalence
to absence of common zeros.

The restriction construction and equivalence are internal consequences of the
published Library representation properties, rational quotient uniqueness
and proved rational-spectrum homeomorphism, together with the independently
submitted actual domain composition construction. Their implemented proofs
are described above. This equivalence concerns the full representation
property for the chosen actual presented affinoids. It does not prove a
presentation theorem for arbitrary abstract affinoids, flatten iterated
rational data into one rational presentation, construct arbitrary domain
base change or tensor products, or establish analytic descent, general
atlases, etale sites or equivariant sites.
