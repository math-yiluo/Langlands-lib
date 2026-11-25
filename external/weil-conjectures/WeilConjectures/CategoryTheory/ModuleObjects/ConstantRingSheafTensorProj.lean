/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheafMonoidal
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLaxMonoidal

/-!
# The tensor isomorphism of `modToSheafModule` on underlying abelian sheaves

Let `(C, J)` be an essentially small site and `T` a commutative ring. On underlying abelian
sheaves, the tensor isomorphism `(M ⊗_T N)^♯ ≅ M^♯ ⊗ N^♯` of
`CategoryTheory.Sheaf.modToSheafModuleTensorIso` is characterised by the projection
`M ⊗ N ⟶ M ⊗_T N` onto the relative tensor product of module objects: precomposed with it, it is
the lax monoidal structure `μ` of the underlying abelian sheaf functor
(`CategoryTheory.Sheaf.tensorObjπ_comp_map_modToSheafModuleTensorIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Opposite Limits Functor.LaxMonoidal
open scoped CategoryTheory.Obj

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (T : Type (u + 1)) [CommRing T]

/-- The unit of sheafification of the underlying abelian presheaf of a presheaf of `T`-modules `Z`,
followed by the comparison `sheafifyModuleCompIso` on underlying abelian sheaves, is the unit of
the sheafification of `Z` as a presheaf of `T`-modules. -/
@[reassoc]
lemma toSheafify_comp_sheafifyModuleCompIso_hom_app (Z : Cᵒᵖ ⥤ ModuleCat.{u + 1} T) :
    toSheafify J (Z ⋙ forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1}) ≫
      (sheafToPresheaf J Ab.{u + 1}).map
        ((sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
          ((sheafifyModuleCompIso J T).hom.app Z)) =
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u + 1} T) Ab.{u + 1}).obj
        (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map (toSheafify J Z) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
      ((sheafifyModuleAdjunction J T).comp (modConstRingSheafEquivalence J T).toAdjunction
        |>.ofNatIsoRight ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (modConstRingSheafEquivalence J T).counitIso
            (sheafToPresheaf J (ModuleCat.{u + 1} T)) ≪≫ Functor.leftUnitor _))
      (sheafificationAdjunction J (ModuleCat.{u + 1} T)) Z
  have h1 (x : Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T)) :
      (Presheaf.modToModule T).map ((modToPresheafMod J T).map
        ((modConstRingSheafEquivalence J T).unit.app x)) ≫
        ((modConstRingSheafEquivalence J T).counitIso.hom.app
          ((modConstRingSheafEquivalence J T).functor.obj x)).hom = 𝟙 _ :=
    congrArg (sheafToPresheaf J (ModuleCat.{u + 1} T)).map
      ((modConstRingSheafEquivalence J T).functor_unit_comp x)
  simp only [Functor.id_obj, ObjectProperty.ι_obj, Functor.comp_obj, sheafifyModuleAdjunction,
    Equivalence.symm_functor, Equivalence.symm_inverse, Adjunction.ofNatIsoRight_unit,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_comp,
    NatTrans.comp_app, Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Functor.comp_map, Category.assoc, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, ObjectProperty.ι_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    sheafificationAdjunction_unit_app] at h
  rw [reassoc_of% h1] at h
  rw [← h, Functor.map_comp, Functor.map_comp]
  rfl

omit [EssentiallySmall.{u + 1} C] in
/-- The tensor map `μ` of the objectwise forgetful functor from presheaves of `T`-modules to
abelian presheaves is the projection `N₁ ⊗_ℤ N₂ ⟶ N₁ ⊗_T N₂`. -/
lemma μ_whiskeringRight_forget₂ (X Y : Cᵒᵖ ⥤ ModuleCat.{u + 1} T) :
    Functor.LaxMonoidal.μ ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u + 1} T) Ab.{u + 1}).obj
      (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})) X Y = Presheaf.moduleTensorπ X Y := by
  ext U : 2
  exact AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)

/-- For presheaves of `T`-modules `X` and `Y`, the sheafification of the projection
`X ⊗_ℤ Y ⟶ X ⊗_T Y`, read through `sheafifyModuleCompIso`, is the tensor map `μ` of the
underlying abelian sheaf functor followed by the tensor map `μ` of sheafification of presheaves
of `T`-modules. -/
@[reassoc]
lemma μ_comp_map_moduleTensorπ_comp_sheafifyModuleCompIso_hom
    (X Y : Cᵒᵖ ⥤ ModuleCat.{u + 1} T) :
    Functor.LaxMonoidal.μ (presheafToSheaf J Ab.{u + 1})
        (X ⋙ forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})
        (Y ⋙ forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1}) ≫
      (presheafToSheaf J Ab.{u + 1}).map (Presheaf.moduleTensorπ X Y) ≫
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
        ((sheafifyModuleCompIso J T).hom.app (X ⊗ Y)) =
    ((sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
        ((sheafifyModuleCompIso J T).hom.app X) ⊗ₘ
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
        ((sheafifyModuleCompIso J T).hom.app Y)) ≫
      Functor.LaxMonoidal.μ (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1}))
        ((presheafToSheaf J (ModuleCat.{u + 1} T)).obj X)
        ((presheafToSheaf J (ModuleCat.{u + 1} T)).obj Y) ≫
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
        (Functor.LaxMonoidal.μ (presheafToSheaf J (ModuleCat.{u + 1} T)) X Y) := by
  rw [← cancel_epi (Functor.OplaxMonoidal.δ (presheafToSheaf J Ab.{u + 1}) _ _),
    Functor.Monoidal.δ_μ_assoc]
  apply ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [Adjunction.unit_naturality_assoc, Adjunction.unit_app_tensor_comp_map_δ_assoc,
    ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, sheafificationAdjunction_unit_app,
    sheafificationAdjunction_unit_app, toSheafify_comp_sheafifyModuleCompIso_hom_app,
    toSheafify_comp_sheafifyModuleCompIso_hom_app,
    reassoc_of% μ_sheafToPresheaf_comp_map_μ_sheafCompose]
  erw [toSheafify_comp_sheafifyModuleCompIso_hom_app]
  have hW : ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u + 1} T) Ab.{u + 1}).obj
      (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map ((toSheafify J X ⊗ₘ toSheafify J Y) ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{u + 1} T)) _ _ ≫
        (sheafToPresheaf J (ModuleCat.{u + 1} T)).map
          (Functor.LaxMonoidal.μ (presheafToSheaf J (ModuleCat.{u + 1} T)) X Y)) =
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u + 1} T) Ab.{u + 1}).obj
        (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map (toSheafify J (X ⊗ Y)) := by
    rw [← sheafificationAdjunction_unit_app, ← sheafificationAdjunction_unit_app,
      ← sheafificationAdjunction_unit_app, ← Adjunction.unit_app_tensor_comp_map_δ_assoc,
      ← Functor.map_comp, Functor.Monoidal.δ_μ, Functor.map_id, Category.comp_id]
  rw [← hW, Functor.map_comp, Functor.map_comp, ← μ_whiskeringRight_forget₂]
  exact (μ_natural_assoc _ _ _ _).symm

/-- On underlying abelian sheaves, `modToSheafModule` does not change morphisms. -/
lemma sheafCompose_map_modToSheafModule_map
    {A B : Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T)} (f : A ⟶ B) :
    (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
      ((modToSheafModule J T).map f) = f.hom :=
  rfl

/-- The inverse of the tensor isomorphism of `sheafifyModule`, precomposed with the projection
onto the relative tensor product, is the sheafification of the projection `X ⊗_ℤ Y ⟶ X ⊗_T Y`. -/
@[reassoc]
lemma tensorObjπ_comp_sheafifyModuleTensorIso_inv_hom (X Y : Cᵒᵖ ⥤ ModuleCat.{u + 1} T) :
    Mod.tensorObjπ ((sheafifyModule J T).obj X) ((sheafifyModule J T).obj Y) ≫
      ((Functor.TensorIso.comp (Presheaf.moduleToModTensorIso (C := C) T)
        (Functor.Monoidal.tensorIso ((presheafToSheaf J Ab.{u + 1}).mapMod _))).iso X Y).inv.hom =
    Functor.LaxMonoidal.μ (presheafToSheaf J Ab.{u + 1}) (Presheaf.toMod T X).X
        (Presheaf.toMod T Y).X ≫
      (presheafToSheaf J Ab.{u + 1}).map (Presheaf.moduleTensorπ X Y) := by
  rw [Functor.TensorIso.comp_iso, Functor.Monoidal.tensorIso_iso, Iso.trans_inv, Iso.symm_inv,
    Functor.Monoidal.μIso_hom, Functor.mapIso_inv, Mod.comp_hom', Functor.mapMod_μ_hom,
    ← Functor.mapModTensorIso_hom_hom]
  erw [Functor.tensorπ_mapModTensorIso_hom_hom_assoc]
  exact congrArg _ (((presheafToSheaf J Ab.{u + 1}).map_comp _ _).symm.trans
    (congrArg _ (Mod.tensorObjπ_tensorObjDesc _ _ _ _)))

/-- `CategoryTheory.Sheaf.tensorObjπ_comp_map_modToSheafModuleTensorIso_hom` on sheafifications
of presheaves of `T`-modules `X` and `Y`: the composite of the tensor isomorphisms of
`sheafifyModule` and of `sheafifyModule ⋙ modToSheafModule`, precomposed with the projection onto
the relative tensor product, is the tensor map `μ` of the underlying abelian sheaf functor. -/
@[reassoc]
lemma tensorObjπ_comp_sheafifyModuleTensorIso_inv_hom_comp_map_hom
    (X Y : Cᵒᵖ ⥤ ModuleCat.{u + 1} T) :
    Mod.tensorObjπ ((sheafifyModule J T).obj X) ((sheafifyModule J T).obj Y) ≫
      ((Functor.TensorIso.comp (Presheaf.moduleToModTensorIso (C := C) T)
        (Functor.Monoidal.tensorIso ((presheafToSheaf J Ab.{u + 1}).mapMod _))).iso X Y).inv.hom ≫
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
        ((Functor.TensorIso.ofIso
          (Functor.Monoidal.tensorIso (presheafToSheaf J (ModuleCat.{u + 1} T)))
          (sheafifyModuleCompIso J T).symm).iso X Y).hom =
    Functor.LaxMonoidal.μ (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1}))
      ((modToSheafModule J T).obj ((sheafifyModule J T).obj X))
      ((modToSheafModule J T).obj ((sheafifyModule J T).obj Y)) := by
  refine (tensorObjπ_comp_sheafifyModuleTensorIso_inv_hom_assoc J T X Y _).trans ?_
  rw [Functor.TensorIso.ofIso_iso_hom, Functor.Monoidal.tensorIso_iso, Iso.symm_inv, Iso.symm_hom,
    Iso.symm_hom, Functor.Monoidal.μIso_inv, Functor.map_comp, Functor.map_comp]
  refine (μ_comp_map_moduleTensorπ_comp_sheafifyModuleCompIso_hom_assoc J T X Y _).trans ?_
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, Functor.map_id, Category.id_comp,
    ← μ_natural, tensorHom_comp_tensorHom_assoc, ← Functor.map_comp, ← Functor.map_comp,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  simp

/-- The projection onto the relative tensor product of module objects over the constant ring sheaf
is natural: `π ≫ (f ⊗ g) = (f ⊗ g) ≫ π`. -/
@[reassoc]
private lemma tensorObjπ_tensorHom_hom_aux
    {M M' N N' : Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T)} (f : M ⟶ M') (g : N ⟶ N') :
    Mod.tensorObjπ M N ≫ (f ⊗ₘ g).hom = (f.hom ⊗ₘ g.hom) ≫ Mod.tensorObjπ M' N' := by
  rw [MonoidalCategory.tensorHom_def, Mod.comp_hom', Mod.tensorObjπ_whiskerRight_assoc,
    Mod.tensorObjπ_whiskerLeft, ← Category.assoc, ← MonoidalCategory.tensorHom_def]

/-- On underlying abelian sheaves, the tensor isomorphism `(M ⊗_T N)^♯ ≅ M^♯ ⊗ N^♯` of
`modToSheafModuleTensorIso`, precomposed with the projection `M ⊗ N ⟶ M ⊗_T N`, is the tensor
map `μ` of the lax monoidal underlying abelian sheaf functor. -/
@[reassoc]
theorem tensorObjπ_comp_map_modToSheafModuleTensorIso_hom
    (A B : Mod (Sheaf J Ab.{u + 1}) (constRingSheaf J T)) :
    Mod.tensorObjπ A B ≫ (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).map
        (((modToSheafModuleTensorIso J T).app A).app B).hom =
      Functor.LaxMonoidal.μ (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1}))
        ((modToSheafModule J T).obj A) ((modToSheafModule J T).obj B) := by
  unfold modToSheafModuleTensorIso
  rw [Functor.TensorIso.ofCompIso_iso_hom]
  simp only [Functor.map_comp, Category.assoc]
  refine (tensorObjπ_tensorHom_hom_aux_assoc J T _ _ _).trans ?_
  refine ((((sheafifyModuleUnderlyingIso J T).inv.app A).hom ⊗ₘ
    ((sheafifyModuleUnderlyingIso J T).inv.app B).hom) ≫=
      tensorObjπ_comp_sheafifyModuleTensorIso_inv_hom_comp_map_hom_assoc J T _ _ _).trans ?_
  refine ((((sheafifyModuleUnderlyingIso J T).inv.app A).hom ⊗ₘ
    ((sheafifyModuleUnderlyingIso J T).inv.app B).hom) ≫=
      (μ_natural (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})) _ _).symm).trans ?_
  rw [tensorHom_comp_tensorHom_assoc, sheafCompose_map_modToSheafModule_map,
    sheafCompose_map_modToSheafModule_map, ← Mod.comp_hom', ← Mod.comp_hom', Iso.inv_hom_id_app,
    Iso.inv_hom_id_app, Mod.id_hom', Mod.id_hom', id_tensorHom_id, Category.id_comp]
  rfl

end CategoryTheory.Sheaf
