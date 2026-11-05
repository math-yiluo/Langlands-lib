# Bounded restrictions from finite-chart section equalizers

This module constructs a bounded restriction from the actual finite-chart section algebra to an original chart covered by finitely many original charts subordinate to the selected members. It proves that the map is independent of the subordinate cover and commutes with original-chart restrictions. The input contains geometric cover data and existing original restrictions; the resulting bounded map is constructed by full-domain descent.

## Source and scope

The original source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §1.2, printed pp.20–21 / PDF pp.17–18, registered as `berkovich-1993-etale-cohomology`, SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. The paragraph after Lemma 1.2.12 defines the Banach section algebra by the equalizer of overlap restrictions and invokes Tate acyclicity for independence of special coverings. Proposition 1.2.13(ii) constructs canonical bounded restrictions when extending the atlas.

The present construction is derived infrastructure for these steps. It uses the actual closed equalizer from `FiniteChartGluingAlgebra`, the full-domain chart restrictions from `AtlasDomainRestrictionNaturality`, and finite full-domain bounded-map descent. The finite family has represented original pairwise intersections. A finite subordinate cover is an explicit additional geometric input, constructed at the end from represented cross intersections when available. No output restriction map is supplied.

This module does not prove Berkovich's intersection-existence Lemma 1.2.12, special-cover admissibility, independence of the section algebra from its defining family, general finite-union affinoid recognition, or maximal-atlas extension. Its independence theorem concerns the subordinate cover used to construct a map from a fixed section algebra.

## Domain restriction formulas

Let `K : Type u` be a complete normed field with ultrametric distance, `X : Type v` a topological space, and `a : IndexedAffinoidAtlas.{u,v,w} K X` an actual affinoid atlas. The three universes remain independent. Let `d : FiniteChartGluingData a`.

For an original chart `k`, an actual full domain `U` over its algebra, and a selected member `i` containing the ambient image `a.chart k '' U.locus`, `memberDomainRestriction` composes the constructed full-domain chart restriction with `d.projection i`. Its source is the actual Banach equalizer and its target is `U.algebra`.

`memberDomainRestriction_eq` proves equality of these full bounded maps for any two containing selected members. The image of `U` lies in their represented overlap by `d.overlap_range`. `domainChartRestriction_comp_original` identifies the two maps from that overlap with the two member formulas. Composing `d.projection_overlap` with the overlap-to-domain restriction proves equality. This argument retains all algebra elements, including information invisible on spectrum points.

`memberDomainRestriction_naturality` proves that this formula commutes with every full-domain inclusion over the same original chart, by the existing naturality of `domainChartRestriction`.

## Finite subordinate original-chart covers and descent

`SubordinateChartCover parent` records a finite size, original chart indices, an assigned selected member for each index, containment in both the parent and assigned member, and coverage of the parent chart range. Empty families and repeated indices are allowed, subject to the same coverage condition.

`domainCover` turns these original charts into an actual finite full-domain cover of `Domain.whole K (a.algebra parent)` using `a.restrictionDomain`. Its domain algebras and arrows are the original presented algebras and bounded restrictions. `domainCover_member_image` records their ambient containment in their assigned selected members.

`localRestriction` composes the original restriction from the assigned member with its equalizer projection. `localRestriction_eq_memberDomainRestriction` identifies this with the preceding full-domain formula, using the original subordinate chart as a common chart. For every full-domain test into two cover objects, naturality and `memberDomainRestriction_eq` prove `localRestriction_compatible`.

`restriction` is the actual bounded algebra map

```text
d.SectionAlgebra → a.algebra parent
```

obtained by `Domain.FiniteCover.glueBoundedAlgHom`. Its boundedness comes from that previously proved descent construction and inverse norm estimate. It requires no nontrivial-valuation or reducedness premise and no Hausdorff assumption on `X`. `original_comp_restriction` recovers each local map as an equality of full bounded algebra homomorphisms.

## Tests, uniqueness, independence, and naturality

`intersectionCover W` intersects an arbitrary full domain `W` over the parent with all cover objects. These actual full-domain intersections cover `W`. `restriction_test` uses algebra separation on this cover to prove that `W.baseMap.comp restriction` is `memberDomainRestriction` for any selected member containing the ambient image of `W`. On each intersection the two structural base-map equations, local recovery, member-domain naturality, and independence of the containing member give the required equality.

`restriction_original` specializes the test formula to any original chart contained in both the parent and a selected member. It recovers the original restriction composed with that member's projection.

`restriction_unique` is full bounded-map uniqueness from the finite full-domain descent theorem. `restriction_eq` applies it to any second subordinate cover: `restriction_test` on each object of the first cover verifies the same local formulas. Thus unrelated choices of finite subordinate cover give exactly the same bounded map.

`restriction_naturality` treats an original child chart contained in the parent, with an independently chosen subordinate cover for the child. On each child cover chart, the original restriction-composition law and `restriction_original` give the child local formula; uniqueness proves the desired bounded-map equation. `restriction_of_member` recovers the original restriction followed by a projection when the entire parent is contained in one selected member.

Finally, `subordinateCoverOfIntersections` constructs a subordinate cover when the parent range is contained in `d.locus` and each literal cross intersection with a selected member is represented by a specified original chart. Containment follows from the intersection equation, and union membership proves coverage. Existence of these intersection charts remains an explicit hypothesis.
