# Transport of arbitrary supplied affinoid atlases

Author: Worker 36.

This module constructs an indexed affinoid atlas on a space homeomorphic
to a space with a supplied actual atlas. It retains the original chart
indices, presented positive-polyradius affinoid algebras and bounded
restrictions. In the published category of monotone chosen atlas maps,
the homeomorphism and its inverse give an actual isomorphism between
the original and transported presentations.

## Source and provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.1, printed pages 13–14 / PDF pages 10–11, gives quasinets,
restricted families and compact nets. Section 1.2, Definition 1.2.3
and Remark 1.2.4(i), printed page 16 / PDF page 13, gives affinoid
atlases and their bounded restrictions. Registered source:
`berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original pages were read; pages 10–11 were reread for this unit.
No source-specific errata note was found in the available project and
Library notes.

This is derived transport infrastructure. It does not assert a new
existence theorem for affinoid domains or identify its chosen-map
category with Berkovich's full strong-morphism category.
`IndexedAffinoidAtlas` and `AffinoidAtlasPresentation` are imported by
Lean name. The source atlas supplies actual quotient algebras, embedded
charts, a compact chart net and bounded restrictions with universal
factorization. The target supplies only its topology and the
homeomorphism; no target atlas or analytic structure is assumed.

## Generic chart and atlas transport

Let `K : Type u` be a complete ultrametric normed field, let
`a : IndexedAffinoidAtlas.{u,v,w} K X`, and let `e : X ≃ₜ Y` with
`Y : Type z`. The coefficient, source-space, target-space and
chart-index universes are independent.

`IndexedAffinoidAtlas.transportChart a e i` is `e ∘ a.chart i`.
`range_transportChart` identifies its range with the image of the
original chart range. `preimage_range_transportChart` recovers the
original range under inverse image by `e`. These formulas prove
`chart_subset_of_transportSubset`, reflecting chart containment,
and `transportChart_subset`, preserving containment.

`transportChartFamily_eq` identifies the transported chart family
with `AtlasTopology.imageFamily e` of the original family.
`isNet_transportChartFamily` applies the generic homeomorphism
invariance of nets, including their restricted pairwise-intersection
families. This proof permits overlapping charts; it uses no
disjoint-component argument.

`transportRestriction` is the original bounded algebra homomorphism,
with the chart-containment proof obtained by inverse image.
`transportRestriction_chart` follows by applying `e` to the original
chart formula. For `transportRestriction_universal`, an admissible
bounded map from the containing chart algebra into any presented
affinoid test algebra satisfies the original image condition:
injectivity of `e` pulls each chart-range witness back to the original
space. The original universal property then gives the unique bounded
factorization. This retains all presented positive-polyradius tests,
including empty or nonstrict spectra.

`IndexedAffinoidAtlas.transport a e` assembles the target atlas:

- Its index type and algebra family are the original ones.
- Its charts are the composite charts; their embeddings are compositions.
- Injectivity of chart-domain indexing follows by inverse image of equal
  transported ranges.
- A Hausdorff neighborhood `U` of `e.symm y` maps to a neighborhood of
  `y`; `e.image U` transports its Hausdorff subspace topology.
- Its chart family is the transported net.
- Its bounded restrictions, universal factorization, and identity and
  composition laws are the original ones with pulled-back containments.

Each transported chart is compact and Hausdorff by the imported
`IndexedAffinoidAtlas.isCompactFamily_chartFamily`, since its algebra
and spectrum are unchanged and its chart is still an embedding.
The lemmas `transport_algebra`, `transport_chart` and
`transport_restriction` expose the retained data and formulas.

## Isomorphism of supplied atlas presentations

For `A : AffinoidAtlasPresentation.{u,v,w} K` and
`e : A.space ≃ₜ Y` with `Y : Type v`,
`AffinoidAtlasPresentation.transport A e` bundles the constructed atlas
and the actual target space. The same-space-universe condition here
allows both objects to belong to the published category; the atlas
construction itself allows the independent target universe `z`.

`transportHom A e` has underlying continuous map `e`, identity chart
index function and the actual bounded identity on every chart
algebra. Its index monotonicity is image preservation of chart
containment. Its chart formula and bounded restriction square follow
from the construction of the target atlas.

`transportInv A e` has underlying continuous map `e.symm`, again with
identity indices and bounded identities. Its monotonicity reflects
chart containment, and its chart formula is `e.symm (e x) = x`.
The bounded restriction square uses the same original restriction;
containment proofs are proof irrelevant.

The selected entry `transportIso A e` pairs these actual arrows.
Both inverse identities use `Hom.ext`: the continuous maps cancel
by the homeomorphism identities, the index functions are identities,
and the dependent bounded pullback families reduce to bounded identity
maps. `transportIso_hom_apply` and `transportIso_inv_apply` expose the
underlying functions as `e` and `e.symm`.

## Scope

An actual source atlas is an explicit input; this module constructs its
transported target atlas. It applies to overlapping supplied atlases and
retains algebraic information beyond spectral points. It does not prove
that an arbitrary homeomorphism between two independently supplied
atlases is analytic, or construct atlas extension, general strong
morphisms, analytic gluing, localization, a structure sheaf, analytic
etale sites or Harris tower spaces. Those remain separate obligations.
