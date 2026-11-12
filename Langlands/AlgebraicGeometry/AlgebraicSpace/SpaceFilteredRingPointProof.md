# Filtered colimits of ring-valued points of algebraic spaces: proof

Author: Worker 208 of the previous FormalGeyser instance (shared draft revision 1
of Task 5208, carried over by the operator's core transfer); staged without
mathematical change by Worker 75.

The theorem `spaceFilteredRingPointComparison` proves exactly
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointComparison`
from `SpaceFilteredRingPointStatement`. It keeps the statement's arbitrary
universe, any commutative base ring `R`, any small filtered diagram of
`R`-algebras with an actual colimit witness, and an arbitrary algebraic space
over `Spec R`. The first clause uses only a locally finite type atlas and the
second only a locally finitely presented atlas. Neither clause assumes
quasi-compactness, quasi-separatedness or separatedness of the space. This is a
proof-only module: it changes neither the statement nor anything the statement
imports.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(31 December 2011), printed p.13 and p.17, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Conrad
says the space case of Theorem 3.4 follows from the scheme case by an étale
descent argument. The proof below is such an argument, built on Mathlib's
limit results for schemes and on Library results about model descent. Most of
the work is done for an arbitrary cofiltered diagram `D` of affine schemes over
a base `S`, with a limit cone `c`. Only the last section specializes to the
spectra of a filtered algebra diagram.

## Sheaf and atlas lemmas

A single flat, locally finitely presented, surjective morphism generates an
fppf covering sieve (`generate_singleton_mem_fppfTopology`). So the sheaf
condition of the space applies to it. Pullback of sections along it is
injective (`pullback_injective`). A section descends along it once its two
pullbacks agree on every pair of maps that the morphism equalizes
(`exists_pullback_eq`). The sheaf-condition and injectivity helpers reuse
`ProductPointsDescent.isSheafFor_singleton` and
`ProductPointsDescent.pullback_injective` from `ProductPointsGluing`; their
local theorem names retain the same statements.

`atlasSection a u` is the section given by an actual scheme point `u` of the
atlas `U`. `exists_atlas_lift` pulls the atlas back along a section `x`. This
gives an étale surjective cover of the test scheme on which `x` is an atlas
point. `exists_affine_refinement` covers a quasi-compact target by finitely
many affine charts and replaces the cover by their finite coproduct.
`exists_affine_atlas_lift` combines the two: over a quasi-compact test scheme,
every section is an atlas point on some affine, étale, surjective cover.
`exists_kernel_pair` recovers the represented kernel pair `R ⇉ U` of the atlas
from `AtlasRelation.exists_kernelPair`. Its two projections are étale, and two
atlas points give the same section exactly when they factor through `R`.

## Eventual equality

`exists_eq_of_limit` handles diagrams `D` of affine schemes over the affine
underlying scheme of a test scheme `T`. If two sections over `T` agree after
pullback to the limit, they agree after pullback to some stage. The atlas only
needs to be locally of finite type.

The proof writes both sections as atlas points on one affine étale surjective
cover `E : W ⟶ T`. It then base changes the diagram along `E`, using the
Library's `TargetLimit.diagram` with the limit cone `coneOfPullback`. Over the
limit, equality of the two sections gives a point of the kernel pair `R`. The
projection `R ⟶ U` is étale, hence locally finitely presented, so
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` descends this
point to a stage. One projection of the descended point equals the first atlas
point there. The other projection agrees with the second atlas point over the
limit. Because `U` is locally of finite type over `S`, the two agree at a later
stage `k` by `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`. The two
sections therefore agree on the base-changed étale cover of stage `k`, and
`pullback_injective` gives equality at stage `k`.

## Points over the limit come from a stage

`exists_stage` assumes a locally finitely presented atlas and an affine limit.
It also assumes `hmodel`: every affine scheme with a locally finitely presented
map to the limit is the pullback of a locally finitely presented,
quasi-compact, quasi-separated model at some stage. Under these hypotheses,
every section over the limit comes from a stage.

The proof first writes the section `x` as an atlas point `w` on an affine,
étale, surjective cover `e`, and applies `hmodel` to `e`. A model at stage `i`
base changes along any transition map into a model at the later stage
(`modelLift`, `isPullback_modelLift`). Four steps then improve the model. Each
step restricts to the indices over the current stage (`overDiagram`,
`overConeIsLimit`) and uses the target base-change diagram of the model.

- `exists_isAffine_model`: the base changes form a cofiltered diagram of qcqs
  schemes with affine transitions and affine limit `W`. By
  `Scheme.exists_isAffine_of_isLimit`, some stage is affine.
- `exists_flat_model`: `e` is étale, hence flat. The Library's
  `AffineLimit.relativeFlatDescent`, applied with the identity as the relative
  target, gives a flat stage.
- `exists_surjective_model`: the image of the model is constructible by
  Chevalley's theorem (`Scheme.Hom.isConstructible_image`), and its preimage in
  the limit is everything. The Library's
  `SchemeFiberGeometry.exists_map_preimage_eq_univ_of_isConstructible` then
  gives a later stage where the preimage of the image is everything. By
  `Scheme.Pullback.range_fst`, the base-changed model is surjective there.
- `exists_lift_model`: once the model is affine, the atlas point `w`
  descends to a morphism `v` from a later model into `U` over `S`, by
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.

The final model `q : V ⟶ D.obj k` is affine, flat, locally finitely presented
and surjective, with `v` lifting `w`. `exists_stage_of_model` glues `v` along
`q`. Its two pullbacks to `V ×_{D_k} V` agree over the limit, because there
both factor through `W` and become the pullbacks of `x`. `exists_eq_of_limit`
on the base-changed kernel-pair diagram makes them agree at a later stage `l`.
The base change of `q` to stage `l` is again an fppf cover. Any two maps that
it equalizes factor through the base-changed kernel pair, so
`exists_pullback_eq` descends the atlas point to a section `y` at stage `l`.
The limit pullback of `y` agrees with `x` after pullback along `e`, so it
equals `x` by `pullback_injective`.

## The ring case

The section `SpaceFilteredRingPoints` takes `D` to be
`SchemeLimitModel.spectrumDiagram R F`, the actual spectra of the stage
algebras over `Spec R`. Its structure maps are `spectrumStructure`. Its limit
is `spectrumCone` with `spectrumConeIsLimit`. The stage test schemes are
definitionally the Library's `ringTest`, and the cone legs are definitionally
the `ringTestMap` of the cocone legs.

- `changeRing_comp` follows from `ringTestMap_comp`, and
  `changeRing_cocone` from it and the cocone equations.
- `exists_changeRing_eq`: two stage-`m` points with equal colimit images agree
  at a later stage. This applies `exists_eq_of_limit` to the spectrum diagram
  restricted to the indices over `m`, with `T = ringTest R (F.obj m)`. The
  identity comparison maps between the over-scheme forms of the same test
  schemes (`pullback_eq_of_comp`) move equality between the forms.
- `spectrum_model` gives `hmodel`. It sends `F` to commutative rings through
  the under-category equivalence followed by `Under.forget`, which preserves
  the filtered colimit. It then applies the Library's
  `schemeFilteredModelExistence`. Affine schemes over the affine limit are
  quasi-compact and quasi-separated over it.
- `exists_changeRing_eq_of_colimit` applies `exists_stage`.

The main theorem gets the first clause from `exists_changeRing_eq` at the
common stage `IsFiltered.max i j`, combined with `changeRing_comp`. The converse
direction uses `changeRing_cocone`. The second clause is
`exists_changeRing_eq_of_colimit`.

## Scope

This proves only the point comparison stated by the target. It does not prove
descent of algebraic spaces, of their morphisms or of their properties along
the colimit, any topology on points, or the specialization to adelic rings.
