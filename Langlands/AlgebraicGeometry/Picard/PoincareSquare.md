# Shear maps on relative products

Authors: Worker 270 wrote the Lean and initial explanation; Worker 417
checked the interfaces and refined the explanation for submission.

Module `Langlands.AlgebraicGeometry.Picard.PoincareSquare` is a helper module
for the proof of `Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`.
For an abelian scheme `B/S` and `S`-schemes `Y`, `T`, it introduces the shear
map `(y, b) ↦ (a y, c y * b)` from `Y ×_S B` to `T ×_S B`, identifies it with a
translation of the base change `B_Y`, and shows that pullback along a shear map
keeps a Picard-zero family Picard-zero on geometric fibres. Everything is in
the namespace `Langlands.AbelianScheme`.

The schemes `S`, `Y` and `T` are arbitrary in universe `u`, and both
`a : Y ⟶ T` and `c : Y ⟶ B.X` are morphisms in `Over S`. The constructions
impose no reducedness, flatness, noetherian or finiteness hypothesis on
these schemes or morphisms. Only the final Picard-zero lemma takes the
explicit additional hypothesis
`stability : PicardZeroPullbackStatement.{u}`. This module does not
prove that hypothesis.

## Products over `S`

* `relativeOver B Y` is the Library total space
  `(relativeSpace B.X.hom).obj Y = Y ×_S B`, viewed as an object of `Over S`
  through `Y`. `relativeFst B Y` and `relativeSnd B Y` are its two projections,
  to `Y` and to `B.X`, as morphisms over `S`.
* `one_left`: the identity point `1 : Y ⟶ B.X` has underlying morphism
  `Y.hom ≫ unitSection B`.
* `relativeSpace_map_fst`, `relativeSpace_map_snd`: the components of the
  induced map `(relativeSpace B.X.hom).map a`.
* `relativeMap B h` is that induced map, viewed as a morphism over `S`;
  `relativeMap_fst` and `relativeMap_snd` give its components. The
  `relativeFst_left`, `relativeSnd_left` and `relativeMap_left` simp lemmas
  identify the underlying scheme morphisms with these chosen pullback
  maps.

## The shear map

* `shear B a c`, for `a : Y ⟶ T` and `c : Y ⟶ B.X` in `Over S`, is the morphism
  `Y ×_S B ⟶ T ×_S B` with first component `pr_Y ≫ a` and second component the
  product `(relativeFst B Y ≫ c) * relativeSnd B Y` in the group of points
  `relativeOver B Y ⟶ B.X`. `shear_fst` and `shear_snd` state the two
  components.
* `relativeSpace_map_shear`: precomposition with the induced map of a morphism
  `h : Y' ⟶ Y` gives `shear B (h ≫ a) (h ≫ c)`.
* `shear_one`: `shear B a 1 = (relativeSpace B.X.hom).map a`.
* `relativeSection_shear`: restricting `shear B a c` along the unit-section
  map `Y ⟶ Y ×_S B` gives `pullback.lift a.left c.left _`.

## Shear maps as translations

* `pointSection B c` is the section of `B_Y = (Over.pullback Y.hom).mapGrp.obj B.toGrp`
  over `Y` that corresponds to `c`, through the Library group isomorphism
  `GroupScheme.baseChangePointsEquiv`.
* `shear_eq_of_comp` recognizes a shear map, transported to the conventional
  total space `B ×_S Y` by `relativeSpaceSymmetry`, from the two components of a
  self-map `t` of `B ×_S Y`. Writing
  `r_Y = (relativeSpaceSymmetry B.X.hom Y).inv`, its hypotheses are
  `t ≫ pr_Y = pr_Y` and
  `t ≫ pr_B = r_Y ≫ ((relativeFst B Y ≫ c) * relativeSnd B Y).left`.
  The conclusion is
  `r_Y ≫ shear B a c = t ≫ r_Y ≫ (relativeSpace B.X.hom).map a`.
  It follows by the two projection equations and `pullback.hom_ext`.
* `symmetryOver B Y` is the inverse symmetry `B ×_S Y ⟶ Y ×_S B` as a morphism
  over `S`; `symmetryOver_fst` and `symmetryOver_snd` compute its composites with
  the two projections.
* `relativeSpaceSymmetry_inv_shear`: on `B ×_S Y`, the shear map equals
  translation of `B_Y` by `pointSection B c` followed by
  the inverse symmetry to `Y ×_S B` and then
  `(relativeSpace B.X.hom).map a`. In the preceding notation, the exact
  equation is
  `r_Y ≫ shear B a c =
    (GroupScheme.translation B_Y (pointSection B c)).left ≫
      r_Y ≫ (relativeSpace B.X.hom).map a`.
  The proof is
  `GroupScheme.baseChangePointsEquiv_translation` from
  `TranslationBaseChange`, rewritten with the two `symmetryOver` lemmas and
  `MonObj.comp_mul`, and then `shear_eq_of_comp`.
* `shearTranslationIso B a c F` is the corresponding isomorphism of line
  bundles on `B ×_S Y`. For any ordinary line bundle `F` on `T ×_S B`
  it has direction
  `r_Y^*((shear B a c)^* F) ≅
    τ_c^*(r_Y^*(((relativeSpace B.X.hom).map a)^* F))`.
  It is built from the preceding equation by pullback composition
  isomorphisms, with the inner composition comparison pulled back along
  the translation. It is an actual isomorphism of ordinary line bundles;
  no rigidification compatibility is asserted.

## Picard-zero condition

* `isGeometricallyPicardZero_shear stability L hL a c`: for a rigidified family
  `L` on `T ×_S B` with `IsPicardZeroFamily B L`, the pullback of its underlying
  bundle along `shear B a c` is Picard-zero on geometric fibres (after the usual
  transport by `relativeSpaceSymmetry`). It takes a proof `stability` of the
  Library proposition `PicardZeroPullbackStatement`, which gives the Picard-zero
  property of the pullback along `a`, and then applies
  `isGeometricallyPicardZero_pullback_translation` to `B_Y` and
  `pointSection B c`. Finally
  `isGeometricallyPicardZero_of_iso` transfers that property along
  `shearTranslationIso.symm` to the sheared pullback. All geometric
  fibres in the conclusion are the actual fibres of
  `(baseChange Y.hom).obj B`. The conclusion concerns the underlying
  ordinary line bundle, and does not construct a rigidification of the
  sheared pullback.

## Provenance

These are internal constructions and compatibility proofs from the
published relative-space pullbacks, group-scheme translation and
`PicardZeroPullbackStatement`, together with the companion
`TranslationBaseChange` module. The mathematical content is that, over the
parameter scheme `Y`, the shear map is the translation of `B_Y` by the point `c`
composed with base change along `a`, and that translates of bundles that are
Picard-zero on geometric fibres are again Picard-zero on geometric fibres.
The projection and unit-section identities are proved directly by the
pullback universal property and the existing group law on points.
The conditional final lemma uses the supplied stability proof as described
above. No independent literature assertion is introduced.

The filename records the intended downstream use in the Poincaré-square
argument. This unit constructs its shear-map infrastructure; it proves
neither a Poincaré tensor-square formula nor
`FieldDualSchemeMapAdditivityStatement`.
