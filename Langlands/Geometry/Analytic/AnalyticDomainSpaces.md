# Analytic domains of saturated presentations as analytic spaces

Author: Worker 21.

An analytic domain `Y` of an analytic space `X` carries the atlas of the
affinoid domains contained in it and a canonical morphism `ν : Y → X`
(Berkovich 1993, §1.3). This module constructs these objects and morphisms for
the saturated presentations underlying the Library's category of analytic
spaces `LocalizedCategory`. It also defines compact domains and the
morphisms that identify their source with the affinoid domain of a chart.
These are the domains used by quasi-étale morphisms and by Berkovich's
compact and distinguished domains.

## Original source

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`,
Definition 1.3.1 and the following remark, printed p.23 / PDF p.20:

> A subset Y of a Φ_k-analytic space X is said to be a Φ-analytic domain if,
> for any point y ∈ Y, there exist Φ-affinoid domains V_1, …, V_n that are
> contained in Y and such that y ∈ V_1 ∩ … ∩ V_n and the set V_1 ∪ … ∪ V_n is
> a neighborhood of y in Y (i.e., the restriction of the net of Φ-affinoid
> domains on Y is a net on Y). … Furthermore, the family of Φ-affinoid domains
> that are contained in a Φ-analytic domain Y ⊂ X defines a Φ_k-affinoid atlas
> on Y, and there is a canonical morphism of Φ_k-analytic spaces ν : Y → X.
> … It is clear that a Φ-analytic domain that is isomorphic to a Φ-affinoid
> space is a Φ-affinoid domain.

The Library realizes analytic spaces by saturated presentations: atlases
containing every affinoid domain that lies in one of their charts
(`HasAllLocalDomains`), in the sense of Berkovich's local saturation `τ̄`
(printed p.17 / PDF p.14, before Proposition 1.2.6). The constructions below use the
charts of such a presentation in place of all affinoid domains. This is a
derived choice, explained in the next section.

## Analytic domains and their atlases

- `IndexedAffinoidAtlas.HasAllLocalDomains.subspaceAtlas`: if an atlas has all
  local domains, so does the Library's atlas `subspaceAtlas` of the charts
  contained in a domain `S`. Proof: a local domain of a contained chart `c` is
  a local domain of the ambient atlas, hence equal to the range of an ambient
  chart `j`. That range lies in the range of `c`, hence in `S`, so `j` is a
  chart of the subspace atlas; its range in `S` is the given local domain.
- `SaturatedAtlasPresentation.AnalyticDomain S` is the Library's
  `OriginalChartDomain` of the atlas of `S`: a subset `D` with the condition
  `IsOriginalChartDomain`, that every point `y ∈ D` lies in finitely many
  charts contained in `D` whose union is a neighbourhood of `y` in `D`.
- `domain S D` is the saturated presentation with space `D` (induced topology)
  and the charts of `S` contained in `D`, with their original algebras and
  bounded restrictions (the Library's `originalDomainPresentation`); it is
  saturated by the previous lemma. `domain_space` records its space.
- `domainInclusion S D : domain S D ⟶ S` is the canonical morphism `ν`: the
  Library's strong inclusion `subspaceStrongInclusion`, whose continuous map
  is the inclusion of the subspace and whose pieces are the original bounded
  restrictions. `domainInclusion_baseMap`, `range_domainInclusion_baseMap`
  and `injective_domainInclusion_baseMap` record that its point map is the
  injective inclusion with image `D`.
- `domainMap S h : domain S D ⟶ domain S E`, for `D ≤ E`, is the strong
  inclusion of nested domains (the Library's `originalDomainStrongMap`), and
  `domainMap_baseMap_val` records its point map.
- `chartDomain S i` is the domain given by the chart `i` (the Library's
  `OriginalChartDomain.ofChart`), an affinoid domain; `chartDomain_carrier`
  records that its subset is the chart range.

Provenance. With charts in place of all affinoid domains, the condition
`IsOriginalChartDomain` agrees with Definition 1.3.1 for Hausdorff spaces, by
the following derived argument (not formalized).

1. Charts of `S` are affinoid domains of `X`, so a domain in the Library's
   sense is an analytic domain.
2. Conversely, let `Y` be an analytic domain and `y ∈ V_1 ∩ … ∩ V_n` as in
   Definition 1.3.1. Each `V_k` is compact, so finitely many charts cover it.
   The affinoid domains of `X` form a net `τ̂` (Proposition 1.2.13(i),
   printed p.21), and Lemma 1.1.2(ii) (printed p.14) writes
   `V_k = U_{k,1} ∪ … ∪ U_{k,m}` with each `U_{k,l} ∈ τ̂` contained in a chart.
   An affinoid domain contained in a chart is an affinoid domain in that
   chart (proof of Proposition 1.2.13(ii)), hence a chart of the saturated
   presentation `S`.
3. The `U_{k,l}` not containing `y` are compact, hence closed in the
   Hausdorff space `X`. So the union of the `U_{k,l}` containing `y` is still
   a neighbourhood of `y` in `Y`, and all of them lie in `Y`.

The atlas of Definition 1.3.1 on `Y` consists of all affinoid domains in `Y`;
`domain S D` uses the charts of `S` contained in `D`, which by the same
argument form a net of affinoid domains of `D` covering every affinoid domain
of `D` by finitely many members.

## Compact domains

Berkovich, §1.1, printed p.13 / PDF p.10: "All compact, locally compact and
paracompact spaces are assumed to be Hausdorff." The Library's atlases are
only locally Hausdorff, so compactness of a domain is required together with
Hausdorffness.

- `IsCompactDomain S D` says that the subset `D` is compact and Hausdorff in
  the induced topology.
- `isCompactDomain_chartDomain`: the affinoid domain of a chart is compact.
  Its range is the image of the compact Banach spectrum, and it is Hausdorff
  because the chart is an embedding, so the range is homeomorphic to the
  Hausdorff spectrum (Mathlib's `IsEmbedding.toHomeomorph`).
- `isCompactDomain_of_eq_iUnion`: if the ambient space is Hausdorff, a domain
  that is a finite union of chart ranges is compact. Without the Hausdorff
  hypothesis this fails: two closed discs glued along their punctured discs
  form a non-Hausdorff space that is a finite union of two charts.

Berkovich's compact analytic domains are the analytic domains that are
compact (hence Hausdorff) topological spaces; in a Hausdorff space they are
exactly the finite unions of affinoid domains contained in them (by
Definition 1.3.1 and compactness), and by the argument above, finite unions
of charts. Only the two implications listed are formalized.

## Domains in the localized category

- `localizedDomainInclusion S D` is the image of `domainInclusion S D` in
  `LocalizedCategory`. `localizedSpaceFunctor_map_localizedDomainInclusion`:
  its underlying continuous map, under the Library's descended space functor,
  is the inclusion of `D`. The proof uses the Library's functor equality
  `localizationFunctor_localizedSpaceFunctor`.
- `IsAffinoidDomainEmbedding j`, for `j : V ⟶ W` in `LocalizedCategory`,
  says that there are a chart `i` of the saturated presentation underlying
  `W` (`localizedObjectEquiv.symm W`) and an isomorphism `e` from `V` to the
  affinoid domain of `i` with `j = e.hom ≫ ν`, where `ν` is the canonical
  morphism of that affinoid domain. This transcribes "V can be identified
  with an affinoid domain in W" for the affinoid domains that are charts of
  the chosen presentation of `W`.
- `isAffinoidDomainEmbedding_localizedDomainInclusion`: the canonical
  morphism of a chart's affinoid domain is such an embedding (with `e` the
  identity). `IsAffinoidDomainEmbedding.iso_comp`: precomposition with an
  isomorphism preserves the property.

Provenance of `IsAffinoidDomainEmbedding`. An affinoid domain `D` of `W` need
not be a chart of the chosen presentation of `W`. When the property is used
with `W` quantified existentially, this is no restriction: adding `D` to the
net of charts gives a net (for a chart `V`, every affinoid domain contained
in `D ∩ V` lies in `V`, and these form a quasinet on `D ∩ V` because `τ̂` is a
net), whose saturation is quasi-isomorphic to the original presentation by
the identity map and has `D` as a chart. This argument is derived and is not
formalized.

## Scope

The coefficient field is a complete ultrametric normed field (trivial
valuation allowed); the universes are `u` for the field and `v`, `w` for
points and chart indices, as in `LocalizedCategory.{u, v, w}`. Not done here:
the universal property of `ν` (factorization of morphisms with image in
`D`); open immersions; preimages of domains under arbitrary morphisms of
`LocalizedCategory`; independence of the chosen presentation; and the
equivalence of `IsCompactDomain` with finite unions of charts.
