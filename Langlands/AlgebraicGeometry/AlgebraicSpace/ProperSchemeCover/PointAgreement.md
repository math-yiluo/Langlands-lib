# Agreement of two morphisms at a point

Helper module for the proof of `ProperSchemeCoverStatement` (weak Chow lemma route).

## Declarations

- `EqAt f g y`: two morphisms of schemes `f g : Y ⟶ Z` agree at the point `y` of `Y`, meaning
  that their composites with the canonical morphism `Spec κ(y) ⟶ Y` are equal.
- `EqAt.comp_right`, `EqAt.symm`, `EqAt.trans`, `eqAt_of_eq`: agreement is preserved by
  postcomposition, is an equivalence relation in the morphisms, and holds for equal morphisms.
- `eqAt_comp_iff`: for `e : A ⟶ Y` and a point `a` of `A`, the composites `e ≫ f` and `e ≫ g`
  agree at `a` exactly when `f` and `g` agree at `e a`.
- `setOf_eqAt_eq_range`: for morphisms `f g : Y ⟶ Z` of schemes over `S` with `Z` separated over
  `S`, the set of points where `f` and `g` agree is the range of the equalizer `equalizer f g ⟶ Y`
  in the category of schemes over `S`.
- `isClosed_setOf_eqAt`: under the same hypotheses this set is closed.

## Proof

`eqAt_comp_iff`: the morphism `Spec κ(a) ⟶ A ⟶ Y` factors as
`Spec κ(a) ⟶ Spec κ(e a) ⟶ Y` (`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`),
and `Spec κ(a) ⟶ Spec κ(e a)` is induced by a field homomorphism, so it can be cancelled on the
left (`Spec_map_field_cancel`).

`setOf_eqAt_eq_range`: if `f` and `g` agree at `y`, the morphism `Spec κ(y) ⟶ Y` over `S`
factors through the equalizer, and the image of the closed point is `y`. Conversely, the two
composites of the equalizer inclusion with `f` and `g` are equal, so by `eqAt_comp_iff` they
agree at every image point. Since `Z` is separated over `S`, the equalizer inclusion is a closed
immersion (Mathlib's instance for equalizers in `Over S`), so its range is closed.
