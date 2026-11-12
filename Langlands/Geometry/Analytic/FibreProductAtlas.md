# The affinoid atlas of a fibre product of analytic spaces

Author: Worker 21.

This module completes the construction of the fibre product `X ×_S Y` of two
compatible strong maps `f : X → S` and `g : Y → S` as an affinoid atlas
presentation. It assumes that:

- the spaces `X`, `Y` and `S` are Hausdorff;
- the atlases of `X` and `Y` contain all local affinoid domains
  (`HasAllLocalDomains`), as the saturated presentations of the Library's
  localized category do.

Under these hypotheses it proves:

- the preimage of two factor charts in the glued space is a finite union of
  pair charts;
- the nonempty pair charts form a net of the glued space;
- the glued space is Hausdorff.

It then assembles the indexed affinoid atlas `FibreProduct.atlas` and the
presentation `FibreProduct.presentation`.

All declarations lie in `Langlands.Analytic.FibreProduct`. The presentations
`A`, `B`, `C` are `AffinoidAtlasPresentation.{u, v, w} K`. The fibre product
presentation lies in `AffinoidAtlasPresentation.{u, max u w, max u w} K`,
because its points and charts are built from chart spectra and pairs of chart
indices.

## Original sources and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, proof of
Proposition 1.4.1, printed p.30 / PDF p.27: "the collection σ' of all affinoid
domains of the form V ×_U U', where V ⊂ Y, U ⊂ X and U' ⊂ X' are Φ-affinoid
domains with φ(V), f(U') ⊂ U, is a net on Y', and there is an evident
Φ_k-affinoid atlas with the net σ'."

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.1,
printed p.1: "In what follows all analytic spaces considered are assumed to be
Hausdorff."

The proofs of the net property and of Hausdorffness are derived; Berkovich
states them without proof. The following choices are derived:

- The affinoid domains `V ∩ f⁻¹(W)` used to refine pairs are charts because
  the atlas contains all local domains. This replaces Berkovich's use of all
  affinoid domains.
- Atlas indices are the nonempty chart ranges, with a chosen pair for each
  range. The Library's atlas structure requires distinct indices to have
  distinct ranges, and different pairs (for example over different base
  charts) can give the same chart. Empty charts are left out.
- The restrictions are those of `FibreProductRestriction`.

## Refining pairs

- `exists_chart_preimage`: let `V_a` be a chart of `X` with
  `f(V_a) ⊆ W_k`, and let `W_m ⊆ W_k` be base charts. Then
  `V_a ∩ f⁻¹(W_m)` is a chart of `X`. It is the locus of the local domain given
  by the Library's inverse image domain (`Domain.pullback`) of the restriction
  domain of `W_m` in `W_k`, and `HasAllLocalDomains.exists_chart` makes it a
  chart.
- `exists_finite_pairs`: for charts `V_a` of `X` and `U_b` of `Y`, the set
  `fst⁻¹(V_a) ∩ snd⁻¹(U_b)` of the glued space is a finite union of pair charts
  whose factor charts lie in `V_a` and `U_b`. Choose base charts
  `W_k ⊇ f(V_a)` and `W_l ⊇ g(U_b)`. The compact set `W_k ∩ W_l` is covered by
  finitely many charts `W_m` inside it (Library `exists_finite_charts_inter`).
  The pairs `(V_a ∩ f⁻¹(W_m), U_b ∩ g⁻¹(W_m))` have the common base `W_m`, and
  `mem_range_chart_iff` shows they cover.

## The net and the Hausdorff property

- `chartFamily f g`: the nonempty chart ranges. `chartFamily_subset`: it lies
  in the family of nonempty sets `fst⁻¹(V) ∩ snd⁻¹(U)` (Library
  `AtlasTopology.preimageProductFamily`), by `range_chart`.
- `isClosed_range_chart`: chart ranges are closed (closed embeddings from
  `FibreProductChartSystem`).
- `locallyRefines_chartFamily`: every member `fst⁻¹(V_a) ∩ snd⁻¹(U_b)` is, near
  each of its points `z`, covered by the finitely many pair charts of
  `exists_finite_pairs` that contain `z`. The pair charts not containing `z`
  form a closed set missing `z`.
- `isNet_chartFamily`: the chart family is a net. The family of preimage
  rectangles is a net (Library `IsNet.preimageProductFamily`), and the Library's
  `IsNet.of_locallyRefines` passes the net property to the refining subfamily.
- `t2Space`: the glued space is Hausdorff, by the Library's
  `IsQuasinet.t2Space_iff`. Each chart range is compact and homeomorphic to a
  spectrum, hence Hausdorff. The intersection of two chart ranges is a closed
  subset of a compact range.

## The atlas

- `AtlasIndex f g`: the members of `chartFamily f g`. `AtlasIndex.rep` is a
  chosen pair with that range (`AtlasIndex.range_rep`).
- `atlas f g hA hB : IndexedAffinoidAtlas K (chartSystem f g).Space`:
  - the algebra and chart of an index are those of its chosen pair;
  - charts are closed embeddings, and distinct indices have distinct ranges by
    construction;
  - the space is Hausdorff, so it is locally Hausdorff;
  - the chart family is the net above (`range_rep_eq_chartFamily`);
  - restrictions are `rangeRestriction`, with the chart equation, universal
    property, identity and composition laws of `FibreProductRestriction`.
- `presentation f g hA hB : AffinoidAtlasPresentation K`: the glued space with
  this atlas.

## Scope

Not constructed here: the projections as strong maps, the universal property of
the fibre product, its saturation and its image in the localized category, and
base change of étale morphisms.
