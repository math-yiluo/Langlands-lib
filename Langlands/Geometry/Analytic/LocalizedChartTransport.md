# Transport of affinoid charts along domain embeddings and isomorphisms

Module `Langlands.Geometry.Analytic.LocalizedChartTransport`.

This module contains helper lemmas for the quasi-étale half of
`Langlands.Analytic.SaturatedAtlasPresentation.SigmaDescStatement`. They move the affinoid
charts of a saturated atlas presentation along strong domain embeddings, into analytic domains,
and along isomorphisms of the localized category. All results are internal lemmas about the
Library's constructions (saturated atlas presentations, their analytic domains and the
localization functor `localizationFunctor` at quasi-isomorphisms). They have no separate
literature source. Everything is in the namespace `Langlands.Analytic.SaturatedAtlasPresentation`,
and `K` is a complete ultrametric normed field.

## Base maps

- `localizedSpaceFunctor_map_localizationFunctor_map_apply`: for a strong map `f : A ⟶ B`, the
  continuous map that `localizedSpaceFunctor` assigns to `localizationFunctor.map f` is the base
  map of `f`. The proof rewrites with the Library lemma `localizedSpaceFunctor_map`; what remains
  holds by definition.

## Charts and strong domain embeddings

- `exists_chart_iso_of_isDomainEmbedding`: let `t : N ⟶ Q` be a strong map of saturated
  presentations that is a domain embedding (`StrongHom.IsDomainEmbedding`), and let `c` be a
  chart of `N`. Then there is a chart `d` of `Q` whose range is `t.baseMap '' range (chart c)`.
  There is also an isomorphism `η` in the localized category between the two chart domains
  `N.domain (N.chartDomain c)` and `Q.domain (Q.chartDomain d)` that commutes with the domain
  inclusions and `localizationFunctor.map t`.

  Proof. `t.target_exists c` gives a chart `m` of `Q` that contains the image of chart `c`. The
  domain-embedding hypothesis says the image is a local domain of `Q` inside `m`
  (`ht.localDomain`). Since `Q` is saturated (`hasAllLocalDomains.exists_chart`), this local
  domain is a chart `d` of `Q`, and its range is the image (`Set.image_preimage_eq_of_subset`).
  So `t` maps the chart domain of `c` into the chart domain of `d`
  (`MapsOriginalDomainCharts`), and `t.restrictDomains` gives a strong map `r` between the two
  chart domains. This `r` is a strong quasi-isomorphism:
  - Its base map is a homeomorphism. It is an embedding because `t.baseMap` is one, and it is
    surjective because the range of `d` is exactly the image.
  - Its chart-image loci are those of `t` (`restrictDomains_chartImageLocus`), and those are
    represented because `t` is a domain embedding. The admissibility conditions match by
    `restrictDomainsBaseMap_admissible_iff`.

  The isomorphism is `η = localizedQuasiIso r hr`. The compatibility with the inclusions comes
  from the Library lemma `restrictDomains_comp_domainInclusion`, after applying
  `localizationFunctor` to it.

## Charts inside analytic domains

- `nestedChart S D c hc`: a chart `c` of `S` whose range lies in an analytic domain `D`, seen as
  a chart of the presentation `S.domain D` (a subspace chart).
- `exists_nestedChart_iso`: the chart domain of `nestedChart S D c hc` inside `S.domain D` is
  isomorphic to the chart domain of `c` in `S`, compatibly with the inclusions into `S`. The
  proof shows that the subspace extension of the nested chart domain is `S.chartDomain c`, as
  sets. The isomorphism is then the Library's `domainNestedLocalizationIso` followed by an
  `eqToIso`. Compatibility follows from `domainNestedLocalizationIso_hom_inclusion` and
  `eqToIso_hom_domainInclusion`.

## Affinoid domain embeddings restricted to charts

- `IsAffinoidDomainEmbedding.chart_comp`: let `D` be an analytic domain of `S`, let
  `j₀ : L(S.domain D) ⟶ W` be an affinoid domain embedding (`IsAffinoidDomainEmbedding`), and
  let `c` be a chart of `S` contained in `D`. Let `m` be the lift of the chart-domain inclusion of
  `c` through `D`. Then `m ≫ j₀` is an affinoid domain embedding.

  Proof. By definition `j₀ = ε.hom ≫ (inclusion of the chart domain of a chart i of
  presentationOf W)` for an isomorphism `ε`. Call that chart domain `Q`. Its full chart `i₀`
  contains every chart of `Q`, so the Library's `localizedTopTargetHomEquiv` turns `ε.hom` into a
  strong map `t : S.domain D ⟶ Q` with `localizationFunctor.map t = ε.hom`. Since this is an
  isomorphism, `t` is a strong quasi-isomorphism (`isQuasiIso_of_isIso_localizationFunctor_map`),
  and in particular a strong domain embedding. Apply `exists_chart_iso_of_isDomainEmbedding` to
  `t` and the nested chart of `c`, and use `exists_nestedChart_iso` to rewrite `m`. Then
  `m ≫ j₀` becomes an isomorphism followed by the inclusion of a chart domain of `Q` into
  `presentationOf W`, through `Q`. This composite is an affinoid domain embedding by the Library
  lemma `isAffinoidDomainEmbedding_domainInclusion_comp`, and precomposition with an isomorphism
  preserves the property (`iso_comp`).

## Compact domains

- `exists_finite_charts_of_isCompact`: a compact analytic domain `D` of `S` is covered by a
  finite family of chart ranges of `S`, each contained in `D`. Proof: by
  `AtlasTopology.isQuasinet_restrictedFamily_iff`, every point of `D` has a finite set of charts
  inside `D` whose union is a neighbourhood of the point within `D`. Compactness
  (`IsCompact.elim_nhds_subcover'`) then selects finitely many of these points.
