# The counit for the glued affine-chart Weil restriction

This is derived construction infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points*, Example 4.2, printed pp.9–10,
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Those pages motivate finite locally free restriction of scalars and its
construction from affine opens. The particular directed-cover construction
below is derived from the Library's actual affine Weil restriction, its
counit and naturality, and Mathlib's gluing theorem. It is not a literal
theorem or proof from the paper.

Let `A → B` be a commutative algebra, finite and projective as an `A`-module,
in an arbitrary common universe `u`. Let `Y` be an actual scheme over `Spec B`
whose structure morphism is locally of finite type. There is no affineness,
separatedness, quasi-separatedness, quasi-compactness or quasi-projectivity
hypothesis on `Y`, and no field, separability, local-ring or topological
hypothesis. Write `G = affineChartWeilRestriction A B Y` for the actual glued
scheme over `Spec A`, and `G_B = ringBaseChange A B G` for its actual scheme
base change.

The main definition `affineChartWeilRestrictionCounit A B Y` constructs an
actual morphism `G_B ⟶ Y` over `Spec B`. It is obtained by gluing the affine
counits, with the published `openOverHomOfLE` relative open inclusions
into `Y`. Neither
this counit nor any of the cover or compatibility data is a supplied
assumption.

The construction first equips the existing chart open cover of `G` with
`Scheme.Cover.LocallyDirected`, using the existing affine Weil-restriction
transition maps. A point of the pullback of two chart maps gives two chart
points with the same image in `G`. The proved exact chart-overlap criterion
supplies a point in a common smaller affine chart. Equality in the pullback
then follows from injectivity of its open-immersion projection. This uses
actual scheme points; it does not identify every scheme pullback with a
set-theoretic pullback.

`affineChartWeilRestrictionCounitCover` pulls that locally directed open
cover back along `G_B ⟶ G`. Its components inherit local directedness from
Mathlib. They are iterated pullbacks, so the module explicitly constructs
`affineChartWeilRestrictionCounitChartMap` from each such component to the
base change of the corresponding original affine Weil-restriction chart.
It uses the two actual pullback projections and their compatibility with
the original chart's structure morphism. The map is over `Spec B`.
`affineChartWeilRestrictionCounitChartMap_natural` proves compatibility with
the pulled-back cover transitions and the base changes of the existing
affine Weil-restriction maps, by equality on both pullback projections.

`affineChartWeilRestrictionLocalCounit` composes this canonical map with the
existing affine counit and the original open inclusion into `Y`.
`affineChartWeilRestrictionLocalCounit_natural` proves agreement along every
directed transition. Its proof uses the preceding pullback compatibility,
affine counit naturality, and compatibility of relative open inclusions.
Mathlib's `glueMorphismsOverOfLocallyDirected` then produces the main global
counit over `Spec B`. `affineChartWeilRestrictionCounit_cover` is its exact
restriction identity on the pulled-back cover.

To express the restriction on the original affine charts rather than the
iterated pullback cover components, the module constructs the reverse map
`affineChartWeilRestrictionCounitChartLift` using the pullback universal
property. Its composite with `CounitChartMap` is the identity, and its
composite with the cover map is the base change of the original chart map.
These two proved identities give `affineChartWeilRestrictionCounit_chart`:
the base change of a chart inclusion followed by the global counit is
exactly that chart's existing affine counit followed by its inclusion
in `Y`.

For every actual test scheme `T` over `Spec A`,
`affineChartWeilRestrictionComparison A B Y T` sends a morphism `p : T ⟶ G`
to the base change of `p` followed by the constructed global counit. Its
values are actual morphisms `T_B ⟶ Y` over `Spec B`.
`affineChartWeilRestrictionComparison_natural` proves contravariant
naturality in every test scheme. On a morphism factoring through any affine
chart, `affineChartWeilRestrictionComparison_chart` identifies this comparison
with the existing affine comparison followed by the original open inclusion.
Both assertions quantify over all test schemes, with no affineness hypothesis
on the test.

This unit constructs the counit and its canonical natural comparison; it
does not assert injectivity or surjectivity of that comparison. In particular,
full representability for the relevant quasi-projective schemes still needs
the finite-fiber affine-neighborhood argument and gluing of inverse maps.
Quasi-projectivity preservation and local or adelic topology comparisons
also remain separate obligations.
