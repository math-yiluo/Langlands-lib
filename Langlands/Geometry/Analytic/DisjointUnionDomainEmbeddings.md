# Domain embeddings of the pieces of a disjoint union

Author: Worker 22.

This internal unit shows that the inclusion of one piece of a disjoint union
of affinoid atlas presentations is an analytic domain embedding in the sense
of `StrongHom.IsDomainEmbedding` (`DomainEmbeddingRecognition`). It shows
this both for the original atlases and for the saturated presentations used
by the localized category. The results are derived infrastructure for the
disjoint-union statements on the analytic étale site. They have no separate
literature source. The coefficient field is any complete ultrametric normed
field, and the field, space and chart-index universes stay independent
wherever the underlying constructions allow it.

## Domain embeddings and saturation

Fix a strong map `f : StrongHom A B` with `hf : f.IsDomainEmbedding`. So
`f.baseMap` is a topological embedding, and on every admissible pair of
original charts `(i, j)` the bounded pullback represents the relative image
`f.chartImageLocus i j`.

- `isEmbedding_pullback`: the spectrum map of each bounded pullback
  `f.pullback i j h` is an embedding. The chart square
  `B.atlas.chart j ∘ comap (f.pullback i j h) = f.baseMap ∘ A.atlas.chart i`
  (`chart_comm`) has an embedding on the right-hand side. Since the target
  chart is an embedding, `IsEmbedding.of_comp_iff` gives the claim.
- `represents_localChartPullback`: for a local full domain `U` of the source
  atlas and a target chart `j` that contains `f.baseMap '' U.locus`, the
  constructed map `f.localChartPullback U j h` represents
  `B.atlas.chart j ⁻¹' (f.baseMap '' U.locus)`. The proof composes the
  representation of the parent chart pullback (from `hf`) with the domain
  representation of `U`. This step uses `Represents.comp_of_injective` and
  the injectivity from `isEmbedding_pullback`. The image in the chosen
  target chart is computed to be `f.baseMap '' U.locus`.
  `represents_changeMapChart` then moves the representation to the chart
  `j`.
- `represents_localDomainPullback`: for local full domains `U` of the
  source and `V` of the target with `f.baseMap '' U.locus ⊆ V.locus`, the
  factored map `f.localDomainPullback U V h` represents
  `V.ambientMap ⁻¹' (f.baseMap '' U.locus)`. This is the previous statement
  for the parent chart of `V`, rewritten along
  `localDomainPullback_comp_baseMap` and cancelled with
  `Represents.of_comp_of_injective` against the injective spectrum map
  of `V`.
- `saturationExtension`: if moreover `hc : f.HasCoherentPullbacks`, then
  `f.saturationExtension hc` is a domain embedding between the saturated
  presentations. Its base map is still `f.baseMap`. Its pullback on a pair
  of saturated charts `(S, T)` is by definition `localDomainPullback` on the
  chosen representatives. So the previous statement applies once the chart
  ranges are rewritten as representative loci (`range_ambientMap`).

## Disjoint unions

For a family `A : I → AffinoidAtlasPresentation K` with nonempty charts,
`AtlasDisjointUnion.isDomainEmbedding_inclusionStrong i` states that
`inclusionStrong A hA i` is a domain embedding. Its base map is
`Sigma.mk i`, which is an embedding (`IsEmbedding.sigmaMk`). On a chart
pair `(c, d)` the relative image locus equals the preimage under the
disjoint-union chart `d` of the range of the chart `⟨i, c⟩`, by
`image_sigmaMk_range`. Its bounded pullback is the atlas restriction, so it
represents this locus by `restriction_represents`, using
`range_subset_of_image_subset`.

For a family `T : J → SaturatedAtlasPresentation K`,
`SaturatedAtlasPresentation.isDomainEmbedding_sigmaCofan_inj T j` states
that the saturated inclusion `(sigmaCofan T).inj j` is a domain embedding.
This inclusion is the saturation extension of the compatible inclusion of
the nonempty-chart replacement family `nonemptyFamily T`. So the
statement follows from the two previous results, with coherence supplied
by `compatibleInclusion`.
