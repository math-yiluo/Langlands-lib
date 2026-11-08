# The chart system of the product of two analytic spaces

Author: Worker 36.

This module builds the gluing data of the product of two spaces with indexed
affinoid atlases. The charts are indexed by pairs of charts. Each pair carries
the affinoid coproduct (completed tensor product over the ground field) of the
two chart algebras. The domain inclusions are componentwise inclusions of
chart ranges. The module verifies the axioms of an `AffinoidChartSystem` from
`AffinoidChartGluing`, defines the two projections from the glued space, and
proves that the charts are closed embeddings when both spaces are Hausdorff.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Proposition 1.4.1, printed p.29 / PDF p.26, states that fibre products of
analytic spaces exist. In the paracompact case its proof takes the triples
`(V, U, U')` of members of locally finite nets with `φ(V), f(U') ⊂ U`, the
affinoid spaces `W_α = V ×_U U'`, and their overlaps. It glues them by
Proposition 1.3.3, printed p.24 / PDF p.21. The absolute product over the
ground field is the case where the base is the one-point space `𝓜(k)` with
its single chart; the triples are then pairs of charts. The equivariant theory
this serves assumes Hausdorff spaces: Berkovich, *Étale
equivariant sheaves on p-adic analytic spaces* (unfinished manuscript, 1996),
registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
PDF SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`,
§1.1, PDF p.1: "In what follows all analytic spaces considered are assumed to
be Hausdorff."

The product chart system follows that indexing, but uses all pairs of charts
of the two atlases rather than locally finite nets. Its verification and the
finite-overlap theorem are derived proofs. Finite overlaps here come from the
Hausdorff hypothesis, which makes chart intersections compact; they do not
come from local finiteness or paracompactness. The atlas, nets and universal
property of the product space are not constructed here.

## Product domains

`Domain.represents_productBaseMap`: for domains `U` of `A` and `V` of `B`, the
structural map `productBaseMap` from the coproduct of `A` and `B` to the
coproduct of the two domain algebras represents the product locus. The Library
writes it as the inverse of the bounded equivalence `productCoproductEquiv`
composed with the structural map of the product domain, which represents that
locus. Representation is preserved by composition with a bounded equivalence
(`Represents.postcomp_equiv`).

## The product chart system

Let `a` and `b` be indexed affinoid atlases on `X` and `Y`.

- `ProductSub a b p q` says that the chart range of `p.1` lies in that of
  `q.1`, and the chart range of `p.2` in that of `q.2`.
- `productAlgebra a b p` is `AffinoidCoproduct.algebra K (a.algebra p.1)
  (b.algebra p.2)`.
- `productRestriction a b p q h` is `productBaseMap` of the two atlas
  restriction domains (`restrictionDomain`). On the two coproduct legs it is
  the leg composed with the atlas restriction
  (`productRestriction_comp_leftMap`, `productRestriction_comp_rightMap`).
- `productRestriction_refl` and `productRestriction_trans` follow from the
  atlas identity and composition laws, by the uniqueness of maps out of the
  coproduct (`AffinoidCoproduct.hom_ext`).
- `range_productRestriction` and `represents_productRestriction`: the
  restriction represents its spectrum image, which is the product locus.
- `leftPoint` and `rightPoint` are the two projections of a point of a product
  chart to points of the factor charts. `leftPoint_pull` and `rightPoint_pull`
  compute them on pulled-back points.
- `mem_range_productRestriction_iff`: a point of the chart `q` lies in the
  image of the subchart `p` exactly when the images of its two projections in
  `X` and `Y` lie in the chart ranges of `p.1` and `p.2`.
- `exists_chart_inter`: a point in two chart ranges of an atlas lies in a chart
  range contained in both, by the net axiom of the atlas.

`productChartSystem a b` is the resulting `AffinoidChartSystem`. Its meet
property applies `exists_chart_inter` in each factor. The chart `(m₁, m₂)`
obtained is a common subchart, and the criterion above places the given point
in its image.

## Projections

`chart_leftPoint_pull` and `chart_rightPoint_pull`: the image in `X` (resp.
`Y`) of the projection of a pulled-back point equals that of the original
point, by the atlas chart equation. Hence the maps
`productFst : (productChartSystem a b).Space → X` and `productSnd` given by
`chart p s ↦ a.chart p.1 (leftPoint s)` and `b.chart p.2 (rightPoint s)` are
well defined on the glued space (`productFst_chart`, `productSnd_chart`). They
are continuous because they are continuous on each chart
(`continuous_productFst`, `continuous_productSnd`).

## Finite overlaps and closed charts

- `exists_finite_charts_inter`: if `X` is Hausdorff, the intersection of two
  chart ranges is compact. The net axiom then covers it by finitely many chart
  ranges contained in it (Library `IsNet.exists_finite_cover_of_subset_inter`).
  Chart ranges determine the charts, so the covering charts form a finite set.
- `productChartSystem_hasFiniteOverlaps`: if `X` and `Y` are Hausdorff, the
  product chart system has finite overlaps. Let `s` in chart `p` be glued with
  `t` in chart `q`. The projections of the common point lie in both chart
  ranges, through the projections `productFst`, `productSnd`. Choose covering
  charts `m₁`, `m₂` from the two finite families. Then `(m₁, m₂)` is a common
  subchart of `p` and `q` from a finite set. The criterion above writes `s` as
  a pullback `v'` from it. Injectivity of the chart `q` shows that the pullback
  of `v'` to `q` is `t`.
- `isClosedEmbedding_productChart`: over Hausdorff spaces the product charts
  are closed embeddings, by `isClosedEmbedding_chart` of `AffinoidChartGluing`.

## Scope

The following remain further work: the atlas of the glued product (chart
ranges, nets, restrictions and their universal property); its Hausdorffness;
the projections as morphisms of analytic spaces; the universal property;
closed subspaces; and fibre products.
