# The affinoid atlas of the glued analytification of a scheme

This unit constructs an `IndexedAffinoidAtlas` on the published glued space
`Space K f` of a scheme `X` locally of finite type over `K`. It assumes the two
gluing properties packaged in `OpenGluing K f`.

## The hypothesis `OpenGluing K f`

`OpenGluing K f` is a `Prop`-valued structure with two fields:

* `isOpenEmbedding`: every canonical map `ι K f U` is an open embedding;
* `range_inter`: for affine opens `U`, `V`,
  `range (ι K f U) ∩ range (ι K f V)` is the union of `range (ι K f W)` over the
  affine opens `W ≤ U ⊓ V`.

These are exactly clauses (2) and (3) of the published (unproved)
`SchemeAnalytificationGluingStatement`. `OpenGluing.injective` extracts the
injectivity of every `ι K f U`.

## The atlas

* `chartImages K f`: the set of images `G.image` of all local charts
  (`SchemeAnalytificationLocalCharts`). It is the index type of the atlas, a
  set of subsets of `Space K f`, so it lives in the universe of the space.
* `chartRep K f T`: a chosen local chart with image `T` (`chartRep_image`,
  `range_chartRep`).
* `schemeAtlas hg`: the atlas with algebra `(chartRep T).algebra` and chart
  `(chartRep T).chart` at the index `T`. Its restriction for `S ⊆ T` is the cross
  map `cross hg.injective (chartRep S) (chartRep T)`. The atlas axioms come from
  the following results:
  * chart embeddings from `LocalChart.isEmbedding_chart` and the open embeddings
    `ι K f U`;
  * injectivity of chart domains from `range_chartRep`;
  * `locallyHausdorff`: each point lies in the open set `range (ι K f U)`, which
    is homeomorphic to the Hausdorff space `U^an`;
  * restriction identities and universality from `cross_chart`,
    `cross_universal`, `cross_self` and `cross_trans`;
  * the net property from `isNet_chartImages` (see below), after
    `range_chartFamily` identifies the chart family with `chartImages K f`.
* `schemeAtlas_hasAllLocalDomains`: the atlas contains all its local domains. A
  local domain `(T, D)` has the same locus as the local chart
  `⟨U, L.extend D⟩`, where `⟨U, L⟩ = chartRep T` (`LocalDomain.extend_locus`).

## The net property

* `image_mem_chartImages`: the image under `ι K f W` of a chart of the saturated
  atlas of `W^an` is a chart image.
* `image_mem_nhdsWithin_of_isOpenEmbedding`: an open embedding `e` sends a
  neighbourhood of `w` within `e ⁻¹' B` to a neighbourhood of `e w` within `B`.
* `isOriginalChartDomain_preimage_image`: for a local chart `G` and an affine
  open `W ≤ G.affineOpen`, the preimage `ι K f W ⁻¹' G.image` is an analytic
  domain of the saturated atlas of `W^an`. By injectivity of `ι K f U`, it is the
  preimage under `localMap` of the chart `L.locus` of the saturated atlas of
  `U^an`, which is an analytic domain by the Library's
  `StrongHom.isOriginalChartDomain_preimage` for the strong map
  `saturatedHom K P_U P_W (restriction f h)`.
* `isNet_chartImages`. Quasinet: a point `ι K f U y` has a finite neighbourhood
  family of charts of the saturated atlas of `U^an`, and the open map
  `ι K f U` carries it to `chartImages K f`. Intersections: a point of
  `G₁.image ∩ G₂.image` lies, by `range_inter`, in `range (ι K f W)` for an
  affine open `W` contained in both affine opens. The two preimages are
  analytic domains of the saturated atlas of `W^an`, and so is their
  intersection. That intersection supplies a finite relative neighbourhood family
  of saturated charts, which `ι K f W` carries into
  `G₁.image ∩ G₂.image`.

## Provenance

Internal. This realizes, for the Library's polynomial-locus model, the atlas
used to glue the affine analytifications in step (3) of the proof of Theorem
3.4.1 of Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean
Fields* (1990), printed p.64/PDF p.78 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`, SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`). It also
realizes the gluing of analytic spaces along open analytic domains of
Proposition 1.3.3 of Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), printed p.24/PDF p.21 (registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`). The only
topological inputs are the two clauses of `OpenGluing`.
