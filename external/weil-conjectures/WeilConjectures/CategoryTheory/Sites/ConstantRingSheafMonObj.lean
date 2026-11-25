/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal

/-! # Constant sheaves of commutative rings as ring objects

The ring-object structure of a constant abelian sheaf on a commutative ring, the
compatibility of the constant-sheaf comparison with these ring objects, and the induced
map from a constant presheaf of rings into the section rings of an internal ring sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The inverse of an isomorphism of monoid objects is a morphism of monoid objects, with
the monoid structures given explicitly.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
theorem IsMonHom.inv_of_hom {D : Type*} [Category D]
    [MonoidalCategory D] {M N : D} (mM : MonObj M) (mN : MonObj N) (e : M ≅ N)
    (h : @IsMonHom _ _ _ M N mM mN e.hom) : @IsMonHom _ _ _ N M mN mM e.inv := by
  let := mM
  let := mN
  infer_instance

/-- A composite of morphisms of monoid objects is a morphism of monoid objects, with the
monoid structures given explicitly.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
theorem IsMonHom.comp_of_monObj {D : Type*} [Category D]
    [MonoidalCategory D] {M N O : D} (mM : MonObj M) (mN : MonObj N) (mO : MonObj O)
    (f : M ⟶ N) (g : N ⟶ O) (hf : @IsMonHom _ _ _ M N mM mN f)
    (hg : @IsMonHom _ _ _ N O mN mO g) : @IsMonHom _ _ _ M O mM mO (f ≫ g) := by
  let := mM
  let := mN
  let := mO
  infer_instance

/-- A lax monoidal functor maps morphisms of monoid objects to morphisms of monoid objects,
with the monoid structures given explicitly.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
theorem Functor.isMonHom_map_of_monObj {D E : Type*} [Category D]
    [Category E] [MonoidalCategory D] [MonoidalCategory E] (F : D ⥤ E) [F.LaxMonoidal]
    {M N : D} (mM : MonObj M) (mN : MonObj N) (f : M ⟶ N)
    (hf : @IsMonHom _ _ _ M N mM mN f) :
    @IsMonHom _ _ _ _ _ (@Functor.monObjObj _ _ _ _ _ _ F _ _ mM)
      (@Functor.monObjObj _ _ _ _ _ _ F _ _ mN) (F.map f) := by
  let := mM
  let := mN
  infer_instance

variable {C : Type*} [Category C] (J : GrothendieckTopology C)

attribute [local instance] Sheaf.monoidalCategory in
/-- The ring object structure of a constant abelian sheaf on a commutative ring is the
sheafification of the constant presheaf of rings.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
theorem constantSheaf_monObjObj_eq [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] (B : Type (u + 1)) [CommRing B] :
    (constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of B) =
      Sheaf.monObj_presheafToSheaf_obj J
        (((Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⋙
          forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙ forget₂ RingCat Ab) :=
  (Functor.monObjObj_comp (Functor.const Cᵒᵖ) (presheafToSheaf J Ab.{u + 1})
    (AddCommGrpCat.of B)).trans
    (congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _ (presheafToSheaf J Ab.{u + 1}) _ _ m)
      (MonObj.ext _ _ (by ext; rfl)))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the constant-sheaf comparison for the forgetful functor from commutative
rings to abelian groups restricts, along the sheafification unit, to the forgotten unit.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
theorem toSheafify_comp_constantCommuteCompose_inv_app_hom
    [HasWeakSheafify J Ab.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})] (B : Type (u + 1)) [CommRing B] :
    toSheafify J ((Functor.const Cᵒᵖ).obj ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1}).obj (CommRingCat.of B))) ≫
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of B)).inv.hom =
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
  have h : ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of B)).inv.hom =
      sheafifyMap J (Functor.constComp Cᵒᵖ (CommRingCat.of B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).inv ≫
        (sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) _).hom := rfl
  rw [h, ← Category.assoc, ← toSheafify_naturality, Category.assoc, sheafComposeIso_hom_fac]
  ext U a
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the constant-sheaf comparison for the forgetful functor from commutative
rings to abelian groups, written as the sheafified unit followed by the counit isomorphism.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
theorem constantCommuteCompose_inv_app_eq
    [HasWeakSheafify J Ab.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.HasSheafCompose (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})] (B : Type (u + 1)) [CommRing B] :
    ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of B)).inv =
      (presheafToSheaf J Ab.{u + 1}).map (Functor.whiskerRight
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
        (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
        (Sheaf.sheafifyRingPresheafIso J ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of B)))).hom := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (ObjectProperty.FullSubcategory.property _)
  rw [toSheafify_comp_constantCommuteCompose_inv_app_hom,
    ObjectProperty.FullSubcategory.comp_hom, Sheaf.sheafifyRingPresheafIso]
  simp only [Functor.comp_obj, Functor.whiskerRight_twice, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, asIso_hom, sheafificationAdjunction_counit_app_val,
    Category.assoc, sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
  ext U a
  rfl

attribute [local instance] Sheaf.monoidalCategory in
/-- The inverse constant-sheaf comparison for the forgetful functor from commutative rings to
abelian groups is a morphism of ring objects.
Source: Stacks 00YV and 03CY (auxiliary; not a blueprint node). -/
theorem isMonHom_constantCommuteCompose_inv_app
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.HasSheafCompose (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})] (B : Type (u + 1)) [CommRing B] :
    @IsMonHom _ _ _ _ _ ((constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of B))
      (Sheaf.monObj_sheafCompose_obj J ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of B))))
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).app (CommRingCat.of B)).inv := by
  rw [constantCommuteCompose_inv_app_eq]
  have h₁ : IsMonHom ((presheafToSheaf J Ab.{u + 1}).map (Functor.whiskerRight
      (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) (forget₂ RingCat.{u + 1} Ab.{u + 1}))) :=
    inferInstance
  have h₂ : IsMonHom (Sheaf.sheafifyRingPresheafIso J ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of B)))).hom :=
    inferInstance
  exact IsMonHom.of_eq _ (constantSheaf_monObjObj_eq J B).symm rfl
    (hf := IsMonHom.comp_of_monObj (Sheaf.monObj_presheafToSheaf_obj J _) _ _ _ _ h₁ h₂)

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory in
/-- A morphism of ring objects from a constant abelian presheaf on a commutative ring into an
internal commutative ring sheaf, as a morphism of presheaves of commutative rings into its
reconstructed section rings.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
def InternalAbelianSheafModule.constantToSectionRings {C : Type v}
    [Category.{w} C] (J : GrothendieckTopology C) [UnivLE.{max v w, u + 1}]
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (B : Type (u + 1)) [CommRing B] (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (φ : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B) ⟶ R.obj)
    (hφ : @IsMonHom _ _ _ _ _ ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ) :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf J R).obj where
  app U := by
    refine CommRingCat.ofHom
      (R := B) (S := (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U)
      { toFun := fun a ↦ φ.app U a
        map_zero' := map_zero _
        map_add' := map_add _
        map_one' := ?_
        map_mul' := ?_ }
    · have h := @IsMonHom.one_hom _ _ _ _ _ _ _ φ hφ
      convert! ConcreteCategory.congr_hom (congr_app h U) (ULift.up 1) using 1
      simp only [Functor.const_obj_obj, Monoidal.tensorUnit_obj,
        Functor.obj.η_def, Category.assoc, NatTrans.comp_app, Functor.const_map_app,
        AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      change (φ.app U) (1 : B) = (φ.app U) ((η[AddCommGrpCat.of B]).hom (ULift.up 1))
      rw [AddCommGrpCat.ringMonObj_one_apply]
      simp
    · intro a b
      have h := @IsMonHom.mul_hom _ _ _ _ _ _ _ φ hφ
      convert! ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b) using 1
  naturality U V f := by
    ext a
    exact ConcreteCategory.congr_hom (φ.naturality f) a

end CategoryTheory
