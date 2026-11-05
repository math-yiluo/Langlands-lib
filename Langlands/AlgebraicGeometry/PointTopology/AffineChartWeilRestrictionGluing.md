# Gluing the actual affine-chart Weil restrictions

This is derived construction infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points*, Example 4.2, printed pp.9–10,
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The example invokes finite locally free restriction of scalars and construction
using affine opens. This module constructs an actual glued scheme from those
affine restrictions. Its locally directed colimit proof is derived from the
Library's actual affine construction and Mathlib's scheme gluing theorem; it
is not a transcription of Conrad's argument.

Let `A → B` be a commutative algebra, finite and projective as an `A`-module,
in an arbitrary common universe `u`. Let `Y` be an actual scheme over `Spec B`
whose structure morphism is locally of finite type. The scheme `Y` need not
be affine, separated, quasi-separated, quasi-compact, or quasi-projective.
No field, separability, local-ring or topological assumption is made.

`affineChartWeilRestrictionDiagram A B Y` is a functor from the ordered category
of all affine opens of `Y` to actual schemes over the smaller base (its codomain
for gluing is `Scheme`). At an affine open `U` its object is the underlying
scheme of `affineWeilRestriction A B (openOver B Y U.val)`. Along `U ≤ V`, its
morphism is the existing `affineWeilRestrictionMap` of the actual relative open
inclusion. Affine opens have locally finite-type structure morphisms and hence
are affine finite-type schemes over the affine base, as required by the affine
constructor. The functor laws follow from the proved laws of these inclusions
and existing coordinate maps. Every transition is a genuine open immersion,
by `affineChartWeilRestrictionDiagram_map_isOpenImmersion`.

`affineChartWeilRestriction A B Y` is an actual object of `Over (Spec A)`.
Its underlying scheme is the colimit of that diagram. Its structure morphism
to `Spec A` is the colimit descent of the actual chart structure morphisms,
packaged as `affineChartWeilRestrictionBaseCocone`. The specified relative chart
morphism is `affineChartWeilRestrictionι A B Y U`. Its underlying scheme map is
the colimit injection, and its compatibility with the structure morphism is
proved by the colimit factorization identity.

`affineChartWeilRestrictionOpenCover` is a genuine open cover of the glued
scheme by precisely these affine Weil-restriction charts, obtained from
`Scheme.IsLocallyDirected.openCover`. Each specified chart map is an open
immersion. `affineChartWeilRestrictionι_naturality` identifies its composite
with an existing transition map with the smaller chart map.
`affineChartWeilRestrictionι_jointly_surjective` proves every point lies in
some chart. `affineChartWeilRestrictionι_eq_iff` proves that two chart points
are equal in the glued scheme exactly when they arise from a point in the
restriction of a common smaller affine open, under the existing coordinate
maps for its two inclusions. These are properties of actual scheme morphisms
and scheme points, rather than an assumed gluing package.

The main gluing hypothesis is proved in
`affineChartWeilRestrictionDiagram_isLocallyDirected`. Given affine opens
`U, V ≤ K` and chart points with equal images in the restriction of `K`, the
intersection `U ∩ V` is affine. The helper
`isAffineOpen_inf_of_common_affine` proves this using the actual cartesian
square of open inclusions and affineness of pullbacks of affine schemes over
an affine scheme. This requires only the common affine upper open `K`, not
separatedness of the ambient `Y`. The same square is cartesian in the relative
category by `openOverHomOfLE_isPullback`. The proved affine
Weil-restriction pullback comparison takes it to a cartesian square over
`Spec A`. Forgetting the base retains that cartesian square, and Mathlib's
`Scheme.exists_preimage_of_isPullback` supplies a point over the two given
points. This is exactly `Functor.IsLocallyDirected.cond`. Mathlib then gives
the actual colimit, open-cover, and overlap results used above.

The imported `openOverHomOfLE` is the actual inclusion of relative
open subschemes over any commutative ring `R`. Its published compatibility with ambient inclusions is reused; identity,
composition, open-immersion, and pullback laws are established here.
The two convenience instances record affineness of an affine relative open
and local finite type of any relative open of a locally finite-type scheme.

This unit does not yet prove that the glued scheme represents the full Weil
restriction of `Y`. In particular, a morphism from a base-changed test scheme
to `Y` must locally over the test base factor through a single affine open;
an arbitrary affine cover alone does not prove that assertion. The finite-fiber
affine-neighborhood argument for the relevant quasi-projective schemes remains
a separate obligation, as do the universal counit, quasi-projectivity
preservation, and local or adelic topology comparisons. No such assertion is
included as an assumed field or as a conclusion of this construction.
