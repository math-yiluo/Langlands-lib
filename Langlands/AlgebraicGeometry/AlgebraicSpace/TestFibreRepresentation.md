# Represented base changes through fibres over a test scheme

Author: Worker 185.

This is derived categorical infrastructure for the affine-atlas step in
Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Lemma 5.10, printed pp.17–18 (registered source
`conrad-2011-weil-grothendieck-adelic-points`). To show that a transformation
of presheaves is representable with étale surjective projections, one fixes a
test scheme `V` and studies the base change along a point of the target over
`V`. This module reduces that base change to a presheaf on schemes over
`V.left` itself. It is not taken from the source.

All declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.TestFibre`.

## Points

`pt c` is a morphism `c : T ⟶ T'` of schemes over `S`, viewed as a section of
the represented presheaf `(schemeYoneda S).obj T'` over `T`. It is the lifted
value `ULift.up c` with its type fixed to the represented presheaf, so that
naturality rewriting applies. `pt_injective`, `exists_pt`, `app_pt` (a natural
transformation out of a represented presheaf evaluates through its Yoneda
element), `map_pt` and `yoneda_map_pt` are the corresponding evaluation lemmas.

## The fibre presheaf

Fix a scheme `S`, a scheme `V` over `S`, presheaves `F` and `G` on schemes over
`S`, a transformation `f : F ⟶ G` and a point `g` of `G` over `V`, that is
`g : (schemeYoneda S).obj V ⟶ G`. A scheme `T` over `V.left` is a scheme over
`S` through `Over.map V.hom`, and `toTest T` is its structure morphism viewed
as a morphism to `V` over `S`; `map_toTest` is its naturality.

`presheaf f g` is the presheaf on schemes over `V.left` whose value at `T` is
the set of sections `x` of `F` over `T` (viewed over `S`) with
`f x = g (toTest T)`, with restriction maps inherited from `F`.
`presheaf_map_val` records the restriction maps.

## Representation of the base change

Let `W` be a scheme over `V.left` and `e` an isomorphism from its represented
presheaf `(schemeYoneda V.left).obj W` to `presheaf f g`. `fst W e` is the
transformation from the represented presheaf of `W` (viewed over `S`) to `F`
given by the universal section `e (𝟙 W)`. `fst_app_map` evaluates it at
morphisms coming from schemes over `V.left`.

For a morphism `b : T ⟶ V` over `S`, `over b` is `T` regarded as a scheme over
`V.left` through `b.left`, and `overIso b` identifies `T` with this scheme
viewed back over `S`; `overIso_hom_toTest` records its compatibility with `b`.

`isPullback` states that the square with top `fst W e`, left
`(schemeYoneda S).map (toTest W)`, right `f` and bottom `g` is a pullback
square of presheaves on schemes over `S`. The proof checks the pointwise
pullback criterion of `Types.isPullback_iff` at every test scheme `T` over `S`:
commutativity is the defining equation of the universal section; uniqueness
and existence of a lift of a pair `(x, b)` with `f x = g b` reduce, by moving
`T` over `V.left` along `b` with `overIso b`, to the bijectivity of `e` at
`over b`.

`toTest_left` records that the projection's underlying scheme morphism is the
structure morphism `W.hom`. Hence étaleness or surjectivity of `W.hom` is
exactly that property of the represented projection.
