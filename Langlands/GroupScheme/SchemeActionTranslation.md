# Translation by a rational point of the acting group

Module `Langlands.GroupScheme.SchemeActionTranslation`, namespace
`Langlands.GroupScheme.SchemeActionTranslation`. This is an internal supporting module for
the proof of `Langlands.GroupScheme.RankOneCentralCoverStatement`, with no literature source.

## Definitions and statements

Let `S` be a scheme, `H : GroupScheme S`, `X : Over S`, `a : SchemeAction H X`, and
`h h' : Over.mk (𝟙 S) ⟶ H.X` sections of the acting group over the base.

- `translate a h : X ⟶ X := a.act (toUnit X ≫ h) (𝟙 X)`, the translation `x ↦ h • x`.
- `comp_translate (w : W ⟶ X)`: `w ≫ translate a h = a.act (toUnit W ≫ h) w`.
- `translate_comp`: `translate a h ≫ translate a h' = translate a (h' * h)`.
- `translate_one`: `translate a 1 = 𝟙 X`.
- Instances `IsIso (translate a h)` and `IsIso (translate a h).left`. The inverse is
  `translate a h⁻¹`.
- `chain_translate`. For scheme points `y₀ ⤳ y₁ ⤳ z` of `X.left` with `y₀ ≠ y₁` and
  `y₁ ≠ z`, the images under `(translate a h).left` again satisfy
  `φ y₀ ⤳ φ y₁ ⤳ φ z`, `φ y₀ ≠ φ y₁` and `φ y₁ ≠ φ z`.
- `isClosed_translate`: translation maps closed points to closed points.

## The implemented proofs

- `comp_translate`: `naturality` of the action, `comp_toUnit`, and `Category.comp_id`.
- `translate_comp`: by `comp_translate`, the composite acts by `toUnit X ≫ h'` on
  `a.act (toUnit X ≫ h) (𝟙 X)`. Then `act_mul` and `MonObj.comp_mul` give the action of
  `toUnit X ≫ (h' * h)`.
- `translate_one`: `MonObj.comp_one` and `act_one`.
- The `IsIso` instances follow from `translate_comp` and `translate_one` with `h⁻¹`, and from
  the forgetful functor `Over.forget S`.
- `chain_translate` and `isClosed_translate`: `(translate a h).left` is an isomorphism of
  schemes, hence a homeomorphism (`Scheme.Hom.homeomorph`). It is continuous, so it
  preserves specialization (`Specializes.map`). It is injective, so it preserves `≠`. It is
  a closed map, so it preserves closed points.
