# Strong inverses on nonempty directed affinoid atlases

Author: Worker 36.

This module constructs an actual isomorphism in
`DirectedAtlasPresentation` from a full strong quasi-isomorphism whose
source atlas has a nonempty original chart index. It derives the
upper-cofinal chart-image condition needed by `cofinalImageIso`; callers
need not supply this extra condition.

The scalar field `K : Type u` is complete, normed and ultrametric.
Underlying spaces have universe `v` and original chart indices universe
`w`. The three universes remain independent. All atlas algebras, bounded
restrictions and all-admissible-pair strong maps are those of the existing
`IndexedAffinoidAtlas` and `AffinoidAtlasPresentation.StrongHom`
constructions. In particular, affinoid-domain representation retains
every finite positive-polyradius presented affinoid test algebra.

The source conventions are Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993):

- Section 1.1, printed pages 13–14 (PDF pages 10–11), defines quasinets
  and nets.
- Definition 1.2.3 and Remark 1.2.4(i), printed page 16 (PDF page 13),
  give the atlas and its domain restrictions.
- Definition 1.2.7, printed page 18 (PDF page 15), gives strong morphisms.
- Definition 1.2.9, printed page 19 (PDF page 16), gives
  quasi-isomorphisms; Proposition 1.2.10 and its proof, printed pages
  19–20 (PDF pages 16–17), explain their role in localization.

The registered original is `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Automatic upper cofinality and strong invertibility under directedness
and the nonempty-index hypothesis are derived consequences. The source
does not state arbitrary strong quasi-isomorphisms are already
isomorphisms before localization.

For an actual atlas `a`, `nonempty_index` obtains a chart index from a
point of the ambient space, using coverage by the quasinet of chart
ranges. This requires `Nonempty X`, without a directedness assumption.
Given `Nonempty a.Index` and `a.HasDirectedCharts`,
`exists_subset_chart_interior` places every compact subset inside the
interior of one original chart range.
`exists_subset_chart` gives containment in the range itself. Both apply
the generic directed-quasinet results of `AtlasTopology.DirectedCompact`
to `a.isNet_chartFamily.1`. They do not construct a new chart algebra.

For a full strong quasi-isomorphism `f : StrongHom A B`,
`IsQuasiIso.hasUpperCofinalImage` assumes directed source charts and
`Nonempty A.atlas.Index`. A target chart range is compact because its
actual spectrum is compact and its chart embedding is continuous.
Its image under the inverse of the ambient homeomorphism is compact.
Source compact containment puts this image in an original source
chart. The published `inverse_admissible_iff` turns this containment
into
`range (B.atlas.chart j) ⊆ f.baseMap '' range (A.atlas.chart i)`.
This proof uses the homeomorphism part of the quasi-isomorphism, not its
domain-factorization part.

`DirectedAtlasPresentation.quasiIsoIso` applies the published
`cofinalImageIso` to this derived cofinality condition. Both atlases are
directed because they are objects of the directed category. The forward
arrow is exactly the original full strong map; the reverse arrow is the
previously constructed full strong inverse, including every admissible
bounded pullback. Both category inverse equations come from that
construction. The accompanying lemmas expose the exact forward map and
inverse continuous base map, and prove the inverse is itself a full
quasi-isomorphism.

`quasiIsoIsoOfNonempty` supplies the same construction when the source
ambient space is nonempty, deriving its chart-index instance through
`nonempty_index`. Its forward arrow is again exactly `f`.

Nonemptiness of the original source chart index is explicit, including
on empty spaces. The module does not claim the resulting existential
chart statements for an empty index. This focused construction does not
establish composition or localization for unrestricted atlases, finite
analytic gluing, maximal atlas construction, or the general étale site.
