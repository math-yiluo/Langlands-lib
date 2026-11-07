# Point-fibre representations after restricting the chart

Module: `Langlands.AlgebraicGeometry.Picard.PointFiberChartRestriction`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

This is an internal construction with no literature assertion. It is the
scheme-level form of the fact that the base change of a chart along the
inclusion of an open subchart is the corresponding open part of the
point-fibre scheme. In stack language: if `P = T ×_𝒳 U` and `V ⟶ U` is a
monomorphism, then `T ×_𝒳 V = P ×_U V`.

Fix `f : X ⟶ S`, schemes `U`, `V`, `T` over `S`, an actual line bundle `L`
on `U ×ₛ X` and an actual line bundle `M` on `T ×ₛ X`.

- `restrictBundle f L j` is the ordinary pullback of `L` along
  `(relativeSpace f).map j` for a map of charts `j : V ⟶ U`.

Now fix a scheme `P` over `T.left` and an isomorphism
`e : schemeYoneda T.left P ≅ pointFiberPresheaf f L M` with the published
actual point-fibre presheaf of `StackAtlas`.

- `pointEquiv e Z` is the resulting bijection between maps `Z ⟶ P` over
  `T.left` and actual fibre points `PointFiberPoints f L M Z` (a map to `U`
  over `S` together with an isomorphism of the pulled-back bundles).
  `pointEquiv_comp` is its naturality: composing with `q : Z' ⟶ Z`
  corresponds to the published restriction of fibre points.
- `universalMap e : P.left ⟶ U.left` is the map underlying the fibre point
  of `𝟙 P`, and `pointEquiv_fst_left` says that the point of `g : Z ⟶ P` has
  underlying map `g.left ≫ universalMap e`.
- `restrictScheme e j` is the scheme pullback of `universalMap e` and
  `j.left`, viewed over `T.left` through `P`, and `restrictSchemeι e j` is its
  map to `P`. When `j.left` is an open immersion this is an open subscheme
  of `P`.
- `toRestrictScheme e j Z x`: a fibre point `x` of the restricted family is
  sent by the published `mapPoints` (composition with `j`) to a fibre point
  of `L`, hence by `pointEquiv` to a map `g : Z ⟶ P`; together with the map
  of `x` into `V` this lifts to `Z ⟶ restrictScheme e j`. Lemmas
  `toRestrictScheme_left_fst`, `toRestrictScheme_left_snd` and
  `toRestrictScheme_comp_ι` record its components.
- `toRestrictScheme_injective` (for `j` a monomorphism) uses the published
  injectivity `mapPoints_injective`.
- `exists_mapPoints_eq`: a fibre point of `L` whose map to `U` factors as
  `a ≫ j` comes from a fibre point of the restricted family with map `a`.
- `toRestrictScheme_surjective`: a map `h` into `restrictScheme e j` gives a
  fibre point of `L` whose map factors through `j` by the pullback square;
  the previous lemma lifts it, and the two components of the lift agree
  with `h`.
- `toRestrictScheme_restrict`: naturality in `Z`, from the published
  `mapPoints_restrict` and `pointEquiv_comp`.
- `restrictIso e j` (for `j` a monomorphism): the resulting isomorphism
  `schemeYoneda T.left (restrictScheme e j) ≅
  pointFiberPresheaf f (restrictBundle f L j) M`, built from these natural
  bijections. It retains the full isomorphism data of fibre points; nothing
  is quotiented.

No hypothesis on `f` or on the schemes is needed besides `Mono j` for the
final isomorphism.
