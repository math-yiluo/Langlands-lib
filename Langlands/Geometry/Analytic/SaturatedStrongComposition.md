# Strong composition on atlases containing all local affinoid domains

Work over a complete ultrametric normed field `K`. Let `A`, `B`, and `C` be
actual `AffinoidAtlasPresentation` objects in the same coefficient, space, and
index universes. Their algebras are the finite positive-polyradius Tate-algebra
quotients and their restrictions are the full affinoid-domain restrictions
of the imported construction. This module constructs composition of the
existing all-admissible-pair `StrongHom` maps when `A.atlas` and `B.atlas`
satisfy `HasAllLocalDomains`. The actual saturation constructor satisfies
that property. The final target `C` is arbitrary.

This is an internal consequence of `SaturatedStrongMapChartChange`, the
bounded chart-change naturality and coherence constructions, and the
elementary chain-pullback API of `DirectedAtlasComposition`. Importing that
last module imposes none of its directed-chart hypotheses here.

For each source chart, `chosenTargetIndex` chooses one admissible target
chart using the strong map's existing `target_exists` field.
`chosenTarget_admissible` records the containment. No monotonicity is claimed
for these choices. For `f : StrongHom A B` and `g : StrongHom B C`,
`saturatedCompPullback` composes the supplied bounded pullbacks along these
two choices and applies the existing actual finite-cover bounded chart-change
construction to every admissible final chart. The underlying map is
`g.baseMap.comp f.baseMap`. `chainPullback_image_chart` and
`saturatedCompPullback_chart` prove the image condition and the ambient chart
equation from the original chart equations.

`chainPullback_isMapChartChange` compares any two admissible chains,
including chains whose intermediate and final charts are unrelated by
inclusion. Source saturation of `A` gives the full universal chart-change
law between the two pullbacks of `f`. Applying `g` preserves that law by
source saturation of `B`. Its conclusion is the full
`IsMapChartChange` relation on the unchanged source chart algebra, with
every bounded affinoid coefficient test retained.
Transitivity and uniqueness of that law give
`saturatedCompPullback_eq_chainChange`: the constructed pullback equals the
change of the bounded composite along any admissible chain to the requested
final chart. This proves equality of complete bounded maps.

For a source-chart inclusion, use the choices for the larger source chart on
both charts. The original restriction equation of `f` identifies the smaller
chain pullback with the larger one followed by the source restriction.
Coefficient naturality of the universal chart-change law and its uniqueness
then prove `saturatedCompPullback_source`. Target coherence, together with
recovery of the original restriction when one target chart is contained in
another, proves `saturatedCompPullback_target`. Combining these gives the
entire two-variable equation `saturatedCompPullback_naturality`.

`saturatedComp` bundles the resulting actual `StrongHom`, including target
existence, all admissible bounded pullbacks, the chart equation, and every
original restriction equation. `saturatedComp_baseMap` records its actual
continuous map. Finally, `saturatedComp_pullback` recovers the literal bounded
composite along every admissible original chart chain by changing to its
own final chart and applying self-recovery.

No reducedness, nonempty-spectrum, represented-image, directedness,
greatest-chart or saturation hypothesis on `C` is imposed. Algebra-map
equality uses the imported universal factorization and bounded descent
results; it is never inferred solely from an equality on spectrum points.
Identity and associativity laws, a category on saturated presentations,
localization and analytic sites remain subsequent work.
