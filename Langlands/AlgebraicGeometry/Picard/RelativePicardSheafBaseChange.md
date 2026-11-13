# Base change of the relative Picard class sheaf

Author: Worker 5067.

Helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionStatement`
(Task 5600). Throughout, `f : X ⟶ S` and `g : S' ⟶ S` are arbitrary morphisms of schemes in
`Scheme.{u}`, and `pullback.snd f g : X ×_S S' ⟶ S'` is the base change of `f` along `g`.
No hypothesis is placed on `f` or `g`.

## Declarations

In namespace `Langlands.AlgebraicGeometry.Picard`:

- `relativeSpace_map_fst f h`: for `h : T ⟶ U` in `Over S`, the Library fibre-product
  functor `relativeSpace f` maps `h` compatibly with the first projections:
  `(relativeSpace f).map h ≫ pullback.fst U.hom f = pullback.fst T.hom f ≫ h.left`.
  This is `pullback.lift_fst`. The `@[reassoc]` attribute also generates
  `relativeSpace_map_fst_assoc`.
- `relativeSpace_baseChange_isPullback f g T`: for `T : Over S'`, the square with
  vertex `T ×_{S'} (X ×_S S')`, projections to `T` and to `X`, and sides `T.hom ≫ g` and
  `f` is a pullback square. It is the vertical pasting of the two defining pullback
  squares.
- `relativeSpaceBaseChangeIso f g : relativeSpace (pullback.snd f g) ≅ Over.map g ⋙ relativeSpace f`,
  a natural isomorphism of functors `Over S' ⥤ Scheme`. Its component at `T` is the
  comparison isomorphism `isoPullback` of the previous pullback square. Naturality is
  checked on both pullback projections by explicit composition chains, using
  `relativeSpace_map_fst` and the Library's `relativeSpace_map_snd`.

In namespace `Langlands.AlgebraicGeometry.Picard.RelativePicard`:

- `classPresheafBaseChangeIso f g : classPresheaf (pullback.snd f g) ≅ (Over.map g).op ⋙ classPresheaf f`.
  The Library presheaf `classPresheaf` is `relativeSpace` followed by the line-bundle class
  group functor and the forgetful functor to types. The isomorphism whiskers the opposite
  of `relativeSpaceBaseChangeIso` with these functors.
- `classSheafBaseChangeIso f g`: an isomorphism of fppf sheaves on `Over S'` from
  `classSheaf (pullback.snd f g)` to the restriction of `classSheaf f` along `Over.map g`
  (`Functor.sheafPushforwardContinuous` for `Scheme.fppfTopology.over S'` and
  `Scheme.fppfTopology.over S`, values in `Type (u+1)`). It is the sheafification of
  `classPresheafBaseChangeIso`, followed by Mathlib's
  `Functor.pushforwardContinuousSheafificationCompatibility`. That isomorphism says that
  restriction along a continuous and cocontinuous functor commutes with sheafification.
  Mathlib provides both properties for `Over.map g` and the `over` topologies.
- `classSheafPresheafBaseChangeIso f g : classSheafPresheaf (pullback.snd f g) ≅ (Over.map g).op ⋙ classSheafPresheaf f`,
  the image of `classSheafBaseChangeIso` under `sheafToPresheaf`.

## Mathematical content

For `T` over `S'`, the scheme `T ×_{S'} (X ×_S S')` is canonically `T ×_S X`. So the presheaf
of line-bundle classes of the base change is the presheaf of `f` restricted to schemes over
`S'`. Since restriction along `Over.map g` commutes with fppf sheafification, the same
identification holds for the Library's fppf Picard class sheaves. This is the usual
compatibility of the relative Picard functor with base change (Faltings–Chai, Chapter I,
Remark 1.5(a), defines `Pic(X/S)` as this fppf sheafification).
