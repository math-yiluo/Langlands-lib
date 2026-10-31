# Bounded atlas maps through directed target charts

This module constructs every admissible local bounded pullback from a monotone
chosen atlas map when the original target chart domains are upward directed.
It works over a complete ultrametric normed field `K` with actual supplied
`AffinoidAtlasPresentation` objects `A` and `B`. The field, space and chart-index
universes `u`, `v` and `w` remain independent. It imports `StrongAtlasMaps` and
reuses its `StrongHom` record and the published full affinoid-domain
factorization property.

The source conventions are V. Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definition 1.2.3 and Remark 1.2.4(i), printed p. 16 /
PDF p. 13, and Definition 1.2.7, printed p. 18 / PDF p. 15, registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The first passage supplies bounded restrictions for contained atlas charts;
the second requires compatible affinoid morphisms for every admissible pair
of source and target charts. The directed-target construction here is derived
infrastructure using these conventions and the domain universal property.
It is not a numbered theorem of the source.

`IndexedAffinoidAtlas.HasDirectedCharts a` is the proposition that every two
original chart ranges of `a` are contained in a third original chart range.
No chosen upper-chart operation is part of this hypothesis.
`hasDirectedCharts_of_top` proves it whenever a supplied original chart contains
every original chart. The construction below needs only this pairwise
upper-bound hypothesis on the target; it imposes no directedness hypothesis
on the source.

For `f : A ⟶ B`, `Hom.pullbackToUpper f i q hs` composes the existing
`f.pullback i` with restriction from an original upper chart `q` to
`f.indexMap i`. It is an actual bounded `K`-algebra homomorphism from the algebra
of `q` to the algebra of `i`. `pullbackToUpper_chart` proves its spectrum square,
and `pullbackToUpper_comp` proves compatibility with a further upper-chart
restriction using associativity and the target restriction composition law.

Suppose the image of source chart `i` lies in target chart `j`, and `q` contains
both `j` and `f.indexMap i`. `factorThroughUpper_existsUnique` applies
`B.atlas.restriction_universal` to the actual presented algebra of source chart
`i` and to `pullbackToUpper`. The spectrum square and the supplied image
containment verify its hypothesis. This constructs a unique bounded map from
the algebra of `j` to that of `i` whose composite with restriction from `q`
is `pullbackToUpper`. Neither the factor map nor its boundedness is an input.

`directedPullback_existsUnique` constructs one bounded map satisfying that
factorization equation at every common upper chart. First choose one upper
chart and its factorization. Given any other upper chart, directedness embeds
the two upper charts into a third. Compose both candidate factorizations with
restriction from that third chart, use the restriction composition law, and
apply `restriction_hom_ext` to cancel restriction from the second upper chart.
This proves the equation at every upper choice. Uniqueness follows by
cancellation at the initially chosen upper chart. The conclusion compares
bounded algebra maps, including information that spectrum-point equality
alone would not determine.

`Hom.directedPullback` chooses the map so constructed.
`directedPullback_comp_restriction` records its factorization equation.
`directedPullback_chart` derives the spectrum square through any common upper
chart and its atlas restriction square. For `directedPullback_naturality`,
enlarge source chart `i` to `i'` and target chart `j` to `j'`, with both pairs
admissible. Choose one upper chart of `f.indexMap i'` and `j'`; monotonicity
of the chosen targets also places `f.indexMap i` there. The original chosen
map's restriction square and the two defining factorization equations make
the desired square commute after restriction from this upper chart.
Cancellation at `j'` proves the equality of bounded maps. Finally,
`directedPullback_selected` recovers exactly `f.pullback i` at the original
selected target, again by restriction cancellation.

`StrongHom.ofDirected f hd` retains `f.baseMap` and uses these constructed
pullbacks at every admissible pair. The original chosen target witnesses
`target_exists`, while the preceding chart and naturality results supply
the two compatibility fields. `ofDirected_pullback_selected` states recovery
of the original selected bounded maps.

`eq_ofDirected_of_pullback_selected` proves uniqueness among strong maps
with the same continuous base map and the same selected bounded pullbacks.
After identifying base maps, strong naturality relates each candidate local
pullback and its selected pullback to every upper chart. Hence it satisfies
the characterizing equations of `directedPullback_existsUnique`. Extensionality
then proves equality of the entire strong maps.
`ofDirected_eq_ofTopChart` applies this uniqueness to the published
`ofTopChart` and its selected-pullback recovery theorem. Its conclusion is
equality of strong maps for any directedness witness and any supplied greatest
target chart.

The input presentations retain genuine positive-polyradius presented affinoid
algebras, spectrum embeddings, a net of chart domains, bounded restrictions,
and the full test-algebra domain factorization property. The only added
hypothesis is pairwise directedness of original target charts; no output
pullbacks, output atlas or gluing result is assumed. This module constructs
strong maps on these supplied atlases. General strong composition, extension
to larger atlases, localization, structure sheaves, étale sites and the Harris
tower remain separate obligations. In particular, the finite gluing and
extended-atlas constructions in Propositions 1.2.6 and 1.2.8 are not supplied
by directedness or by this module.
