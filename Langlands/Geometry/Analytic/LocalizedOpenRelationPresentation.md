# The glued analytic space

For gluing data `R : LocalizedOpenRelation K`, this module constructs the affinoid
atlas of the glued space and the glued analytic space. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation`.

## The atlas

`atlas R : IndexedAffinoidAtlas K (Space R)` has

- index type `ChartImage R`, algebra of `T` the algebra of `T.rep`, chart
  `chartMap T`;
- chart embeddings: `ι` is an open embedding and the charts of the pieces are
  embeddings; distinct indices have distinct ranges since the range of `chartMap T`
  is `T` itself;
- local Hausdorffness (`locallyHausdorff`): the image under the open embedding
  `ι m` of a Hausdorff neighbourhood in a piece;
- the net property (`isNet_chartImages`, after `range_chartMap_family` identifies
  the chart family with the images of the charts of the pieces): the quasinet
  condition is transported from a piece by the open embedding `ι m`; for two chart
  images `T₁ = c₁.image` and `T₂ = c₂.image` and a point `ι m z` of `T₁ ∩ T₂`, the
  trace `{w | ι m w ∈ T₁ ∩ T₂}` on `Z m` is an analytic domain
  (`isOriginalChartDomain_preimage_image` and `IsOriginalChartDomain.inter`), its
  charts give finitely many charts of the piece around `z`, and their images are
  chart images contained in `T₁ ∩ T₂` whose union is a neighbourhood of `ι m z` in
  `T₁ ∩ T₂` (`Langlands.Analytic.SchemeAnalytification.image_mem_nhdsWithin_of_isOpenEmbedding`);
- restrictions `rho S.rep T.rep`, with `rho_chart`, `rho_universal`, `rho_self`
  and `rho_comp` giving the restriction axioms.

`atlas_hasAllLocalDomains`: a local domain of a chart image `T` is a local domain
of the chart `T.rep` of a piece, hence a chart of that piece (the pieces are
saturated), and its image is again a chart image.

`presentation R` is the saturated presentation with space `Space R` and atlas
`atlas R`, and `glued R` is its object in the localized category.

## Provenance

Derived from the proof of Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Proposition 1.3.3, printed pp.24–25 / PDF pp.21–22
(`berkovich-1993-etale-cohomology`). There the glued space is given the atlas whose net
consists of the subsets `V` contained in the image of a single piece `Xᵢ` whose inverse
image in `Xᵢ` is an affinoid domain (continuation of the proof on printed p.25 / PDF
p.22). These are not all affinoid domains of the glued space: an affinoid domain may
meet several pieces. Correspondingly, the Lean atlas `atlas R` is indexed by the images
in the glued space of the charts of the given saturated presentations of the pieces, one
index for each image.
