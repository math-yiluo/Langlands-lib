/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Multifunctor

/-!
# Functors commuting with the tensor product, without coherence

For monoidal categories `C` and `D` and a functor `F : C ⥤ D`, a *tensor isomorphism* for `F`
(`CategoryTheory.Functor.TensorIso F`) is a natural isomorphism of bifunctors
`F (X ⊗ Y) ≅ F X ⊗ F Y`, with no compatibility with the associators or unitors required.
This is the structure that is often enough to transport statements about tensor products along
an equivalence of categories, and it is much easier to produce than a monoidal structure.

## Main definitions

* `CategoryTheory.Functor.TensorIso`: the type of tensor isomorphisms for `F`.
* `CategoryTheory.Functor.TensorIso.ofComponents`: a tensor isomorphism from components
  `F (X ⊗ Y) ≅ F X ⊗ F Y` natural in `X` and `Y`.
* `CategoryTheory.Functor.Monoidal.tensorIso`: the tensor isomorphism of a strong monoidal
  functor, given by the inverse of its tensorator `μIso`.
* `CategoryTheory.Functor.TensorIso.comp`: the tensor isomorphism of `F ⋙ G` from tensor
  isomorphisms for `F` and `G`.
* `CategoryTheory.Functor.TensorIso.ofIso`: transport of a tensor isomorphism along a natural
  isomorphism `F ≅ F'`.
* `CategoryTheory.Functor.TensorIso.ofCompIso`: a tensor isomorphism for `G` from tensor
  isomorphisms for `P` and `P ⋙ G`, given a functor `Q` with `Q ⋙ P ≅ 𝟭`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- A tensor isomorphism for a functor `F` between monoidal categories: a natural isomorphism
`F (X ⊗ Y) ≅ F X ⊗ F Y` of bifunctors, with no coherence condition. -/
abbrev TensorIso (F : C ⥤ D) : Type _ :=
  (postcompose₂.obj F).obj (curriedTensor C) ≅
    (((whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D)

namespace TensorIso

variable {F : C ⥤ D}

/-- A tensor isomorphism for `F` from isomorphisms `F (X ⊗ Y) ≅ F X ⊗ F Y` natural in `X` and
`Y`. -/
noncomputable def ofComponents (e : ∀ X Y : C, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (natural_left : ∀ {X X' : C} (f : X ⟶ X') (Y : C),
      F.map (f ▷ Y) ≫ (e X' Y).hom = (e X Y).hom ≫ F.map f ▷ F.obj Y)
    (natural_right : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y'),
      F.map (X ◁ g) ≫ (e X Y').hom = (e X Y).hom ≫ F.obj X ◁ F.map g) :
    F.TensorIso :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (e X) (natural_right X))
    fun f ↦ NatTrans.ext (funext fun Y ↦ natural_left f Y)

/-- The component `F (X ⊗ Y) ≅ F X ⊗ F Y` of a tensor isomorphism. -/
abbrev iso (τ : F.TensorIso) (X Y : C) : F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y :=
  (τ.app X).app Y

/-- The tensor isomorphism of a composite `F ⋙ G`, from tensor isomorphisms for `F` and `G`:
`G (F (X ⊗ Y)) ≅ G (F X ⊗ F Y) ≅ G (F X) ⊗ G (F Y)`. -/
noncomputable def comp (τF : F.TensorIso) {G : D ⥤ E} (τG : G.TensorIso) : (F ⋙ G).TensorIso :=
  (postcompose₂.obj G).mapIso τF ≪≫ (((whiskeringLeft₂ E).obj F).obj F).mapIso τG

@[simp]
lemma comp_iso (τF : F.TensorIso) {G : D ⥤ E} (τG : G.TensorIso) (X Y : C) :
    (τF.comp τG).iso X Y = G.mapIso (τF.iso X Y) ≪≫ τG.iso (F.obj X) (F.obj Y) :=
  rfl

/-- Transport of a tensor isomorphism along a natural isomorphism `F ≅ F'`:
`F' (X ⊗ Y) ≅ F (X ⊗ Y) ≅ F X ⊗ F Y ≅ F' X ⊗ F' Y`. -/
noncomputable def ofIso (τ : F.TensorIso) {F' : C ⥤ D} (e : F ≅ F') : F'.TensorIso :=
  ((postcompose₂.mapIso e).app (curriedTensor C)).symm ≪≫ τ ≪≫
    ((((whiskeringLeft₂ D).mapIso e).app F).app (curriedTensor D) ≪≫
      (((whiskeringLeft₂ D).obj F').mapIso e).app (curriedTensor D))

@[simp]
lemma ofIso_iso_hom (τ : F.TensorIso) {F' : C ⥤ D} (e : F ≅ F') (X Y : C) :
    ((τ.ofIso e).iso X Y).hom =
      e.inv.app (X ⊗ Y) ≫ (τ.iso X Y).hom ≫ (e.hom.app X ⊗ₘ e.hom.app Y) := by
  simp [ofIso, tensorHom_def]

/-- A tensor isomorphism for `G : D ⥤ E` from tensor isomorphisms for `P : C ⥤ D` and
`P ⋙ G`, given `Q : D ⥤ C` with `Q ⋙ P ≅ 𝟭 D`:
`G (A ⊗ B) ≅ G (P Q A ⊗ P Q B) ≅ G (P (Q A ⊗ Q B)) ≅ G (P Q A) ⊗ G (P Q B) ≅ G A ⊗ G B`. -/
noncomputable def ofCompIso {P : C ⥤ D} {G : D ⥤ E} {Q : D ⥤ C} (e : Q ⋙ P ≅ 𝟭 D)
    (τP : P.TensorIso) (τPG : (P ⋙ G).TensorIso) : G.TensorIso :=
  (postcompose₂.obj G).mapIso
      (((((whiskeringLeft₂ D).mapIso e).app (Q ⋙ P)).app (curriedTensor D) ≪≫
        (((whiskeringLeft₂ D).obj (𝟭 D)).mapIso e).app (curriedTensor D)).symm ≪≫
      (((whiskeringLeft₂ D).obj Q).obj Q).mapIso τP.symm) ≪≫
    (((whiskeringLeft₂ E).obj Q).obj Q).mapIso τPG ≪≫
    ((((whiskeringLeft₂ E).mapIso (isoWhiskerRight e G)).app (Q ⋙ P ⋙ G)).app
        (curriedTensor E) ≪≫
      (((whiskeringLeft₂ E).obj G).mapIso (isoWhiskerRight e G)).app (curriedTensor E))

@[simp]
lemma ofCompIso_iso_hom {P : C ⥤ D} {G : D ⥤ E} {Q : D ⥤ C} (e : Q ⋙ P ≅ 𝟭 D)
    (τP : P.TensorIso) (τPG : (P ⋙ G).TensorIso) (A B : D) :
    ((ofCompIso e τP τPG).iso A B).hom =
      G.map ((e.inv.app A ⊗ₘ e.inv.app B) ≫ (τP.iso (Q.obj A) (Q.obj B)).inv) ≫
        (τPG.iso (Q.obj A) (Q.obj B)).hom ≫ (G.map (e.hom.app A) ⊗ₘ G.map (e.hom.app B)) := by
  simp only [ofCompIso, Iso.trans_symm, mapIso_symm, Iso.trans_assoc, mapIso_trans, Iso.app_hom,
    NatIso.trans_app, Iso.trans_hom, Iso.symm_hom, mapIso_inv, Iso.app_inv, mapIso_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, postcompose₂_obj_obj_obj_obj, curriedTensor_obj_obj,
    whiskeringLeft₂_obj_obj_obj_obj_obj, id_obj, comp_obj, postcompose₂_obj_map_app_app,
    whiskeringLeft₂_obj_map_app_app_app, curriedTensor_obj_map, whiskeringLeft₂_map_app_app_app_app,
    curriedTensor_map_app, whiskeringLeft₂_obj_obj_map_app_app, whiskerRight_app, tensorHom_def,
    Category.assoc, map_comp]
  rw [← G.map_comp_assoc, whisker_exchange, G.map_comp_assoc]

end TensorIso

/-- The tensor isomorphism `F (X ⊗ Y) ≅ F X ⊗ F Y` of a strong monoidal functor, the inverse
of its tensorator. -/
noncomputable def Monoidal.tensorIso (F : C ⥤ D) [F.Monoidal] : F.TensorIso :=
  TensorIso.ofComponents (fun X Y ↦ (Monoidal.μIso F X Y).symm)
    (fun f Y ↦ (OplaxMonoidal.δ_natural_left F f Y).symm)
    (fun X _ _ g ↦ (OplaxMonoidal.δ_natural_right F X g).symm)

@[simp]
lemma Monoidal.tensorIso_iso (F : C ⥤ D) [F.Monoidal] (X Y : C) :
    (Monoidal.tensorIso F).iso X Y = (Monoidal.μIso F X Y).symm :=
  rfl

end CategoryTheory.Functor
