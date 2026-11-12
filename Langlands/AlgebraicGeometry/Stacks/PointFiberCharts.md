# Maps into representing schemes of actual point fibres

Module: `Langlands.AlgebraicGeometry.Stacks.PointFiberCharts`.

Author: Worker 3694, for task `5b9ad399-34f2-4314-bb39-902f491aad01`.

This internal module supplies general tools for the published scheme-atlas
predicate `Stacks.HasLocallyFiniteTypeSmoothSchemeAtlas`. Everything is stated
for an arbitrary category-valued pseudofunctor
`F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1}` on the full slice of
schemes over `S : Scheme.{u}`, with a chart object `ξ` over `U : Over S` and a
test object `η` over `T : Over S`. The point fibre is the published
`Stacks.pointFiberPresheaf F ξ η` on `Over T.left`. Its points over `Z`
(`Stacks.PointFiberPoints`) are pairs of an actual map to `U` over `S` and an
actual isomorphism of pulled-back objects.

The declarations generalize the published line-bundle constructions in
`Picard.PointFiberChartRestriction`, `Picard.PointFiberTestReduction` and
`Picard.FiniteTypePicardStackAtlasAssembly` to an arbitrary pseudofunctor. The proofs follow the same arguments, with the
coherent restriction maps of the published `PseudofunctorPointFiber`,
`PseudofunctorPointFiberAtlasRestriction`, `PseudofunctorPointFiberObjectIso`
and `PseudofunctorPointFiberTestChange` modules. No literature assertion is
formalized here.

## Maps into a representing scheme

Fix `P : Over T.left` and a natural isomorphism
`e : schemeYoneda T.left P ≅ pointFiberPresheaf F ξ η`.

- `pointEquiv e Z : (Z ⟶ P) ≃ PointFiberPoints F ξ η Z` is the component of `e`
  at `Z`, after removing the universe lift of the scheme Yoneda presheaf.
  `pointEquiv_comp` records naturality: precomposition with `q : Z' ⟶ Z`
  corresponds to coherent restriction along the iterated-slice image of `q`.
- `universalMap e : P.left ⟶ U.left` is the chart map of the point classified
  by the identity of `P`. `pointEquiv_fst_left` shows that the point classified
  by any `g : Z ⟶ P` has chart map `g.left ≫ universalMap e`.
- `range_subset_of_point`: if some scheme `Z` over the test carries a fibre
  point, the image of `Z` in the test lies in the image of `P`, because the point
  is classified by a map `Z ⟶ P` over the test.

## Restricting the chart along a monomorphism

For `j : V ⟶ U` over `S`, `restrictObj j ξ` is the pulled-back chart object
`(F.map j.op.toLoc).toFunctor.obj ξ`.

- `restrictScheme e j` is the fibre product of `universalMap e` and `j.left`,
  over the test through `P`; `restrictSchemeι e j` is its projection to `P`.
- `toRestrictScheme e j Z` sends a point of the restricted chart over `Z` to a
  map into `restrictScheme e j`. Its first component is the map into `P`
  classifying the point after composing its chart map with `j`; its second
  component is the original chart map into `V`.
- For a monomorphism `j`, this map is injective (`toRestrictScheme_injective`),
  using injectivity of the published `mapPoints`. It is surjective for every
  `j` (`toRestrictScheme_surjective`): a map into `restrictScheme` gives a point
  of the original fibre whose chart map factors through `j`, and
  `exists_mapPoints_eq` lifts it, inverting the published `atlasComparison`.
  `toRestrictScheme_restrict` proves compatibility with every slice morphism.
- `restrictIso e j`, for monic `j`, is the resulting natural isomorphism
  `schemeYoneda T.left (restrictScheme e j) ≅ pointFiberPresheaf F (restrictObj j ξ) η`
  on the entire slice.

## Comparisons

- The existing `Picard.PicardGroupoid.representingIso e e'`, imported from
  `Picard.FiniteTypePicardStackAtlasAssembly`: two schemes over `B` whose scheme Yoneda presheaves
  are isomorphic to the same presheaf are isomorphic over `B`, by full
  faithfulness of the lifted Yoneda embedding.
- `pointFiberPresheafIsoOfChartIso c η` and
  `pointFiberPresheafIsoOfTestIso ξ c` whisker the published object-change
  isomorphisms by the iterated-slice functor, for isomorphisms `c` of chart or
  test objects.
- `pointFiberPresheafBaseChangeIso ξ g η`, for `g : T' ⟶ T` over `S`, compares
  the point fibre of the pulled-back test object `restrictObj g η` with the
  original point fibre restricted along `Over.map g.left`. It composes the
  published `basePresheafIso` with the published `iteratedSliceMapIso g`.
- `pullbackRepresentationIso ξ g e`: the pullback `Over.pullback g.left P`
  represents the point fibre of `restrictObj g η`. It composes the published
  `schemeYonedaPullbackIso` with `e` and the previous comparison.
- `mem_range_of_chartPoint e g a c x`: let `g : T' ⟶ T` and `a : T' ⟶ U` be maps
  over `S`, and let `c` be an actual isomorphism between the pullbacks of `ξ`
  along `a` and of `η` along `g`. Then every point `x` of `T'` maps under `g` into
  the image of `P`. The pair `(a, c)`, restricted to the scheme `T'.left` over
  `T.left`, is a fibre point, so `range_subset_of_point` applies.

## Coproduct charts

Let `V : ι → Over S` with `ι : Type u`, and let `sigmaOver V` be the published
coproduct chart with component inclusions `sigmaOverι V i`. Let `ξ` be a chart
object over the coproduct and `ξs i` objects over the components, with actual
isomorphisms `c i : restrictObj (sigmaOverι V i) ξ ≅ ξs i`.

`smooth_of_coproductChart` assumes that, for one test object `η`, each `ξs i`
has some representing scheme smooth over the test. Then every scheme `P`
representing the point fibre of `ξ` against `η` is smooth over the test. The
pullback along `universalMap e` of the coproduct open cover is an open cover of
`P`. Its `i`-th member is `restrictScheme e (sigmaOverι V i)`, which represents
the fibre of `restrictObj (sigmaOverι V i) ξ` by `restrictIso` (the component
inclusions are monomorphisms). Through `c i` and `representingIso` it is
isomorphic over the test to the given smooth representing scheme for `ξs i`.
Smoothness is local on the source.
