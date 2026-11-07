# Gluing schemes along a common open subscheme

Author: Worker 105.

Helper module for the proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedOfFiniteTypeStatement`
(the counterexample to the closedness assertion of Conrad's Corollary 5.7). It contains no
statement from the literature. It specializes Mathlib's scheme gluing (`Scheme.GlueData`,
built from `CategoryTheory.GlueData'`) to one simple case.

## Setting

Fix an index type `J : Type u`, schemes `U j` for `j : J`, a scheme `W` and open immersions
`g j : W ⟶ U j`. Glue the `U j` by identifying the copies `g j (W)` of `W`. In Mathlib's
terms every overlap `V i j` (for `i ≠ j`) is `W`, every transition map `t i j` is the
identity of `W`, and the cocycle condition holds trivially. Mathlib's `GlueData'` only asks
for the data off the diagonal.

## Declarations

Namespace `Langlands.AlgebraicGeometry.CommonOpenGluing`.

- `pullback_fst_eq_snd`: for a monomorphism `h`, the two projections of `pullback h h`
  agree.
- `glueData'`: the `GlueData'` with overlaps `W`, inclusions `g i`, transition maps `𝟙 W`.
  The triple-overlap maps `t'` are `pullback.lift fst fst`; the cocycle condition reduces to
  `pullback_fst_eq_snd` for the monomorphism `g i`.
- `f'_isOpenImmersion`: the overlap inclusions of the associated `GlueData` are open
  immersions. Off the diagonal they are the `g i`; on the diagonal they are identities.
- `glueData : Scheme.GlueData`, `glued` (the glued scheme) and `ι j : U j ⟶ glued`
  (an open immersion, by Mathlib's `Scheme.GlueData.ι_isOpenImmersion`).
- `f_eq`, `tf_eq`: for `i ≠ j` the inclusion `f i j` of the overlap is `g i`, and
  `t i j ≫ f j i` is `g j`, up to the `eqToHom` coming from the `dite` in
  `GlueData.ofGlueData'`.
- `g_ι`: `g i ≫ ι i = g j ≫ ι j`. For `i ≠ j` this is Mathlib's `glue_condition`, rewritten
  with `f_eq` and `tf_eq`.
- `exists_of_comp_eq`: for `i ≠ j`, if `a : T ⟶ U i` and `b : T ⟶ U j` have the same
  composite to the glued scheme, then there is `w : T ⟶ W` with `w ≫ g i = a` and
  `w ≫ g j = b`. The proof uses Mathlib's `vPullbackConeIsLimit`: the overlap is the
  pullback of `ι i` and `ι j`.
- `hom_ext`: morphisms out of the glued scheme agree when they agree on every `U j`.
- `desc`, `ι_desc`: morphisms `m j : U j ⟶ Y` with `g i ≫ m i = g j ≫ m j` glue to
  `desc m hm : glued ⟶ Y` with `ι j ≫ desc m hm = m j`. This is
  `Scheme.Cover.glueMorphisms` for the open cover by the `ι j`; its compatibility
  hypothesis on `pullback (ι i) (ι j)` comes from `exists_of_comp_eq`, or from
  `pullback_fst_eq_snd` when `i = j`.
- `exists_ι_apply`: every point of the glued scheme lies in the image of some `ι j`.
- `isOpenCover_opensRange`: the images of the `ι j` form an open cover.
- `opensRange_inter_opensRange`: for `i ≠ j`, the intersection of the images of `ι i` and
  `ι j` is the image of `W` (via `g i ≫ ι i`). One inclusion applies `exists_of_comp_eq` to
  the pullback of `ι i` and `ι j`; the other is `g_ι`.
- `isCompact_opensRange_inter`: if `W` and all `U j` are quasi-compact, so are these
  intersections.
- `quasiSeparatedSpace`: if all `U j` are affine and `W` is quasi-compact, the glued scheme
  is quasi-separated (Mathlib's `Scheme.quasiSeparatedSpace_of_isOpenCover`).
- `exists_lift_of_isLocalRing`: a morphism `Spec S ⟶ glued` with `S` local factors through
  some `ι j`. The image of the closed point lies in some piece; every point of `Spec S`
  specializes to the closed point, so its image lies in that open piece too, and the
  morphism lifts through the open immersion (`IsOpenImmersion.lift`).
