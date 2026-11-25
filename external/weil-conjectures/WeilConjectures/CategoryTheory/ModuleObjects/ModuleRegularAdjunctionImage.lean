/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ModuleRegularUnitIso
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-! # Images of projectors on the direct image of the regular module

Let `F ⊣ G` be a monoidal adjunction between categories of module objects, with `F` strong
monoidal and reflecting isomorphisms. Consider endomorphisms `e` of `G (regular S)` whose images
`I_e` are trivialized by `F`, in the sense that `F I_e ⟶ F G (regular S) ⟶ regular S` is an
isomorphism. Then:

* `CategoryTheory.Adjunction.image_tensor_regular_isIso`: if the multiplication map
  `I_{e₁} ⊗ I_{e₂} ⟶ G (regular S)` is fixed by `e₃`, it induces an isomorphism
  `I_{e₁} ⊗ I_{e₂} ≅ I_{e₃}`;
* `CategoryTheory.Adjunction.unit_image_regular_isIso`: if the unit of `G` is fixed by `e`, it
  induces an isomorphism from the monoidal unit onto `I_e`.

In both cases the proof applies `F`, and uses that the mate of the lax monoidal structure of `G`
is the inverse of the strong monoidal structure of `F`.
Source: blueprint lem-kernel-condensed-projector-descent.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R : C} [MonObj R] [IsCommMonObj R]
    {S : D} [MonObj S] [IsCommMonObj S]
    {F : Mod C R ⥤ Mod D S} {G : Mod D S ⥤ Mod C R} (adj : F ⊣ G)
    [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal] [F.ReflectsIsomorphisms]
    [HasImages (Mod C R)]

/-- If the images of `e₁, e₂, e₃` are trivialized after applying `F`, and the multiplication
map from `image e₁ ⊗ image e₂` to `G (regular S)` is fixed by `e₃`, then its corestriction to
`image e₃` is an isomorphism.
```
                       m := (ι ⊗ ι) ≫ μ ≫ G.map mul
image e₁ ⊗ image e₂ ─────────────────────────────────▶ G (regular S) ⟲ e₃
          ╲                                                   ▲
           ╲ m ≫ factorThruImage e₃.asHom  (≅)                      │ image.ι e₃.asHom
            ╲──────────────────────▶ image e₃ ────────────────╯
```
The hypothesis `h` is `m ≫ e₃.asHom = m`, so `m` factors through `image e₃`; the theorem says that
the factor is an isomorphism.
Source: blueprint lem-kernel-condensed-projector-descent. -/
theorem image_tensor_regular_isIso (e₁ e₂ e₃ : End (G.obj (Mod.regular S)))
    [IsIso (F.map (image.ι e₁.asHom) ≫ adj.counit.app (Mod.regular S))]
    [IsIso (F.map (image.ι e₂.asHom) ≫ adj.counit.app (Mod.regular S))]
    [IsIso (F.map (image.ι e₃.asHom) ≫ adj.counit.app (Mod.regular S))]
    (h : ((image.ι e₁.asHom ⊗ₘ image.ι e₂.asHom) ≫ μ G (Mod.regular S) (Mod.regular S) ≫
        G.map (Mod.regularMul S)) ≫ e₃.asHom =
      (image.ι e₁.asHom ⊗ₘ image.ι e₂.asHom) ≫ μ G (Mod.regular S) (Mod.regular S) ≫
        G.map (Mod.regularMul S)) :
    IsIso (((image.ι e₁.asHom ⊗ₘ image.ι e₂.asHom) ≫ μ G (Mod.regular S) (Mod.regular S) ≫
        G.map (Mod.regularMul S)) ≫ factorThruImage e₃.asHom) := by
  rw [← isIso_iff_of_reflects_iso _ F]
  have : IsIso (F.map (((image.ι e₁.asHom ⊗ₘ image.ι e₂.asHom) ≫
        μ G (Mod.regular S) (Mod.regular S) ≫ G.map (Mod.regularMul S)) ≫
        factorThruImage e₃.asHom) ≫
        F.map (image.ι e₃.asHom) ≫ adj.counit.app (Mod.regular S)) := by
    rw [← F.map_comp_assoc, Category.assoc, image.fac, h, F.map_comp, F.map_comp,
      Category.assoc, Category.assoc]
    erw [adj.counit_naturality]
    erw [adj.map_μ_comp_counit_app_tensor_assoc]
    rw [← δ_natural_assoc,
      tensorHom_comp_tensorHom_assoc, Mod.regularMul_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map (image.ι e₃.asHom) ≫ adj.counit.app (Mod.regular S))

/-- If the image of `e` is trivialized after applying `F` and the unit of `G` is fixed by `e`,
then the unit of `G` corestricts to an isomorphism from the monoidal unit onto `image e`.
```
𝟙_C ──ε──▶ G (regular S)
  ╲              │ e
   ╲ ≅           ▼
    ╲─────▶ image e ──ι──▶ G (regular S)
```
The composite `ε ≫ e` equals `ε` by `h`, so `ε` factors through `image e`, and the factor
`ε ≫ factorThruImage e` is an isomorphism.
Source: blueprint lem-kernel-condensed-projector-descent. -/
theorem unit_image_regular_isIso (e : End (G.obj (Mod.regular S)))
    [IsIso (F.map (image.ι e.asHom) ≫ adj.counit.app (Mod.regular S))]
    (h : ε G ≫ (e).asHom = ε G) :
    IsIso (ε G ≫ factorThruImage (e).asHom) := by
  rw [← isIso_iff_of_reflects_iso _ F]
  have : IsIso (F.map (ε G ≫ factorThruImage e.asHom) ≫
      F.map (image.ι e.asHom) ≫ adj.counit.app (Mod.regular S)) := by
    rw [← F.map_comp_assoc, Category.assoc, image.fac, h]
    erw [adj.map_ε_comp_counit_app_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map (image.ι e.asHom) ≫ adj.counit.app (Mod.regular S))

end CategoryTheory.Adjunction
