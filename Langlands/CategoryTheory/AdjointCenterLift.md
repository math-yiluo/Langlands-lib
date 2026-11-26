# Lifting central components through a faithful left adjoint

Module `Langlands.CategoryTheory.AdjointCenterLift`, namespace `Langlands.Renard`.

This is a general categorical lemma used in the proof of `LeviCenterComponentsLiftStatement`
(module `Langlands.Representation.CuspidalSupport.LeviCenterComponentsLift`), the existence part
of the Harish-Chandra homomorphism of Renard, *Représentations des groupes réductifs p-adiques*
(French version dated 9 July 2026), VI.10.5, printed p.213 / PDF p.219. It is not taken from the
source; it is a derived argument stated for arbitrary categories.

## Statement

`exists_map_eq_center_app_of_detecting`. Let `C` be an abelian category, `D` a category,
`I : C ⥤ D` a faithful functor and `adj : I ⊣ R` an adjunction. Let `z : CatCenter D` (Mathlib's
`End (𝟭 D)`) and `X : C`. Assume:

- for every object `Y` and every nonzero `φ : X ⟶ Y` there are an object `Q`, a morphism
  `s : Q ⟶ X` with `s ≫ φ ≠ 0`, and an endomorphism `f : Q ⟶ Q` with `I.map f = z.app (I.obj Q)`.

Then there is `y : X ⟶ X` with `I.map y = z.app (I.obj X)`.

Composition is diagrammatic: `f ≫ g` is `g ∘ f`.

## Proof as implemented

Write `η = adj.unit.app X : X ⟶ R (I X)` and `ẑ = adj.homEquiv _ _ (z.app (I.obj X))`, the
adjunct of the component of `z`.

1. `η` is a monomorphism, because `I` is faithful (Mathlib's instance
   `Adjunction.unit_mono_of_L_faithful`).
2. For `Q`, `s` and `f` as in the hypothesis, `s ≫ ẑ = (f ≫ s) ≫ η`. Indeed, by naturality of the
   unit, `s ≫ ẑ` is the adjunct of `I.map s ≫ z.app (I.obj X)` and `(f ≫ s) ≫ η` is the adjunct of
   `I.map (f ≫ s)`. Naturality of `z` along `I.map s` (`CatCenter.naturality`) and
   `I.map f = z.app (I.obj Q)` show that the two morphisms of `D` agree.
3. `ẑ ≫ cokernel.π η = 0`. Otherwise the hypothesis applied to `φ = ẑ ≫ cokernel.π η` gives
   `Q`, `s`, `f` with `s ≫ φ ≠ 0`. By step 2, `s ≫ φ = (f ≫ s) ≫ η ≫ cokernel.π η = 0`, a
   contradiction.
4. In the abelian category `C`, the monomorphism `η` is a kernel of its cokernel, so
   `ẑ = y ≫ η` with `y = Abelian.monoLift η ẑ _`.
5. The adjunct of `I.map y` is `y ≫ η` (naturality of the unit), which is `ẑ`, the adjunct of
   `z.app (I.obj X)`. Since `adj.homEquiv` is injective, `I.map y = z.app (I.obj X)`.
