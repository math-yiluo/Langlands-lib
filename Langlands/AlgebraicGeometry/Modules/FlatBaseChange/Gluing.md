# Flat base change of higher direct images: gluing

Helper module for the proof of
`Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement`
(see `FlatHigherDirectImageBaseChangeProof.md`). Namespace
`Langlands.AlgebraicGeometry.Modules.FlatBaseChange`.

## Declarations

- A local instance: pullback along a flat morphism preserves finite limits, by
  the published theorem `flatPullbackExact` (Stacks Project, tag 02N4).
- `isIso_higherDirectImageBaseChange_congr`: invertibility of a component of
  `higherDirectImageBaseChangeNatTrans b f f' p w n` depends only on the
  morphisms `b` and `p`, not on the proof `w` or the instance arguments
  (`subst`, then `Iff.rfl`).
- `flat_of_comp_isOpenImmersion f i h`: if `f ≫ i` is flat and `i` is an open
  immersion, then `f` is flat. By Mathlib's `Flat.iff_flat_stalkMap` and
  `Scheme.Hom.stalkMap_comp`, the stalk map of `f ≫ i` at `x` is the stalk map
  of `i` at `f x`, an isomorphism of rings, followed by that of `f`; Mathlib's
  `RingHom.Flat.comp_iff_of_bijective_right` cancels the bijective factor.
- `isIso_higherDirectImageBaseChange f g f' g' h M n`: for a cartesian square
  `h : IsPullback g' f' f g` with `f` quasi-compact and separated, `g` and `g'`
  flat (instance arguments) and a quasi-coherent `M`, the component at `M` of
  `higherDirectImageBaseChangeNatTrans g f f' g' h.w n` is an isomorphism, in
  every degree `n`.

## Proof of the gluing step

By the Library's `isIso_of_affineOpenPullbacks`, it suffices that for every
point `y` of `Y'` some open immersion `c : Spec T ⟶ Y'` with `y` in its image
makes `c^*` of the component an isomorphism. The Library's
`exists_affineOpenFactorization g y` supplies open immersions
`x : Spec R ⟶ Y` and `c : Spec T ⟶ Y'` with `y` in the image of `c` and a ring
map `φ : R ⟶ T` with `c ≫ g = Spec.map φ ≫ x`.

1. **Moving `c` into the square.** Let `q : X'_T ⟶ X'` and `fT : X'_T ⟶ Spec T`
   be the projections of `X'_T = X' ×_{Y'} Spec T`. The square of `c` has an
   invertible transformation at `g'^* M` by
   `isIso_higherDirectImageBaseChange_of_isOpenImmersion`. By
   `isIso_pullback_map_higherDirectImageBaseChange_iff`, `c^*` of the
   component for `g` is invertible iff the component for the composite square
   over `c ≫ g` (top map `q ≫ g'`) is.
2. **Refactoring the composite square.** Let `pR` and `fR` be the projections
   of `X_R = X ×_Y Spec R`, and `q' : X'_T ⟶ X_R` the lift of `q ≫ g'` and
   `fT ≫ Spec.map φ`. Pasting gives a cartesian square
   `IsPullback (q' ≫ pR) fT f (Spec.map φ ≫ x)`, and Mathlib's
   `IsPullback.of_right` gives the cartesian square
   `IsPullback q' fT fR (Spec.map φ)`.
3. **Flatness and finiteness.** `Spec.map φ` is flat by
   `flat_of_comp_isOpenImmersion`, since `Spec.map φ ≫ x = c ≫ g` is flat; `q'`
   is flat as its base change. `fR` is quasi-compact and separated as a base
   change of `f`. All pullbacks involved therefore preserve finite limits by
   the local instance.
4. **The two pieces.** The square of `Spec.map φ` has an invertible
   transformation at `pR^* M` by `isIso_higherDirectImageBaseChange_affine`
   (module `FlatBaseChange.AffineCase`); the square of the open immersion `x`
   has an invertible transformation at `M` by
   `isIso_higherDirectImageBaseChange_of_isOpenImmersion`. Applying
   `isIso_pullback_map_higherDirectImageBaseChange_iff` to these two squares
   makes the component for the composite square over `Spec.map φ ≫ x` (top map
   `q' ≫ pR`) invertible.
5. **Comparison.** Since `Spec.map φ ≫ x = c ≫ g` and `q' ≫ pR = q ≫ g'`,
   `isIso_higherDirectImageBaseChange_congr` transfers this to the composite
   square of step 1.

This follows the gluing of Stacks Project, Lemma 02KH, step 1: the global
comparison map is fixed first, and invertibility is checked locally. The
proof uses only the standard axioms.
