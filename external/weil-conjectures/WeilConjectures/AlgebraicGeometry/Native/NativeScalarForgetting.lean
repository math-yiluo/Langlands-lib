/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-! # Forgetting ambient scalars in native module sheaves

## References

* Stacks Project, Tags 03CW, 03CY and 03EK

## Implementation details

The inverse equips an internal module over the underlying abelian ring sheaf with the scalar
action obtained by restricting the ring action to the (central) constant scalar sections; the
sectionwise action then factors through the tensor product over the scalar field, and the
native action is obtained by sheafification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.ScalarForgetting

universe v w

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  (K : Type u) [CommRing K]
  [UnivLE.{max v w, u}]
  [HasSheafify J (ModuleCat.{u} K)] [HasSheafify J Ab.{u}]
  [(J.W (A := ModuleCat.{u} K)).IsMonoidal] [(J.W (A := Ab.{u})).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private noncomputable abbrev U : Sheaf J (ModuleCat.{u} K) ⥤ Sheaf J Ab.{u} :=
  sheafCompose J (forget₂ (ModuleCat.{u} K) Ab.{u})

variable (B : Sheaf J (ModuleCat.{u} K)) [MonObj B]

private noncomputable abbrev sectionAction (M : Mod (Sheaf J (ModuleCat.{u} K)) B) (V : Cᵒᵖ) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{u} K)) B M.X) ≫
    (sheafToPresheaf J (ModuleCat.{u} K)).map (Mod.act M.X)).app V

omit [UnivLE.{max v w, u}] [HasSheafify J Ab.{u}]
    [(J.W (A := Ab.{u})).IsMonoidal] in
private theorem sectionAction_one (M : Mod (Sheaf J (ModuleCat.{u} K)) B)
    (V : Cᵒᵖ) (r : K) (x : M.X.obj.obj V) :
    sectionAction J K B M V
      ((MonObj.one (X := (sheafToPresheaf J (ModuleCat.{u} K)).obj B)).app V r ⊗ₜ[K] x) =
        r • x := by
  let P := ((sheafToPresheaf J (ModuleCat.{u} K)).mapMod B).obj M
  exact ConcreteCategory.congr_hom
    (congr_app (Mod.one_act (A := (sheafToPresheaf J (ModuleCat.{u} K)).obj B) P.X) V)
    (r ⊗ₜ[K] x)

private theorem sectionAction_forget (M : Mod (Sheaf J (ModuleCat.{u} K)) B)
    (V : Cᵒᵖ) (b : B.obj.obj V) (x : M.X.obj.obj V) :
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u}))
        ((U J K).obj B) ((U J K).obj M.X) ≫
      (sheafToPresheaf J Ab.{u}).map (Mod.act (((U J K).mapMod B).obj M).X)).app V).hom
        (b ⊗ₜ[ℤ] x) = sectionAction J K B M V (b ⊗ₜ[K] x) := by
  simp only [Functor.act_mapMod_obj, Functor.map_comp, ← Category.assoc]
  rw [μ_sheafToPresheaf_comp_map_μ_sheafCompose]
  rfl

private theorem sectionAction_linear {M N : Mod (Sheaf J (ModuleCat.{u} K)) B}
    (f : ((U J K).mapMod B).obj M ⟶ ((U J K).mapMod B).obj N)
    (V : Cᵒᵖ) (b : B.obj.obj V) (x : M.X.obj.obj V) :
    (f.hom.hom.app V).hom (sectionAction J K B M V (b ⊗ₜ[K] x)) =
      sectionAction J K B N V (b ⊗ₜ[K] (f.hom.hom.app V).hom x) := by
  let G := (sheafToPresheaf J Ab.{u}).mapMod ((U J K).obj B)
  have h := ConcreteCategory.congr_hom (congr_app (Mod.act_hom (G.map f)) V)
    (b ⊗ₜ[ℤ] x)
  change (f.hom.hom.app V).hom
      ((((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u}))
        ((U J K).obj B) ((U J K).obj M.X) ≫
        (sheafToPresheaf J Ab.{u}).map
          (Mod.act (((U J K).mapMod B).obj M).X)).app V).hom (b ⊗ₜ[ℤ] x)) =
      ((((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u}))
        ((U J K).obj B) ((U J K).obj N.X) ≫
        (sheafToPresheaf J Ab.{u}).map
          (Mod.act (((U J K).mapMod B).obj N).X)).app V).hom
            (b ⊗ₜ[ℤ] (f.hom.hom.app V).hom x)) at h
  simpa only [sectionAction_forget] using h

private theorem presheafMonoid_eq :
    (sheafToPresheaf J Ab.{u}).monObjObj ((U J K).obj B) =
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} K) Ab.{u}).obj
        (forget₂ (ModuleCat.{u} K) Ab.{u})).monObjObj
          ((sheafToPresheaf J (ModuleCat.{u} K)).obj B) := by
  apply MonObj.ext
  simp only [Functor.obj.μ_def, Functor.map_comp, ← Category.assoc]
  rw [μ_sheafToPresheaf_comp_map_μ_sheafCompose]
  rfl

private theorem pointMonoid_eq (V : Cᵒᵖ) :
    (Monoidal.MonFunctorCategoryEquivalence.functorObjObj
      ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)) V).mon =
    (forget₂ (ModuleCat.{u} K) Ab.{u}).monObjObj
      (Monoidal.MonFunctorCategoryEquivalence.functorObjObj
        ((sheafToPresheaf J (ModuleCat.{u} K)).obj B) V).X := by
  have h := presheafMonoid_eq J K B
  change (Monoidal.MonFunctorCategoryEquivalence.functorObjObj _ V).mon = _
  rw [h]
  rfl

private noncomputable instance sectionRing (V : Cᵒᵖ) : Ring (B.obj.obj V) :=
  InternalAbelianSheafModule.ring
    (Monoidal.MonFunctorCategoryEquivalence.functorObjObj
      ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)) V).X

private theorem sectionRing_mul (V : Cᵒᵖ) (b c : B.obj.obj V) :
    b * c = (MonObj.mul (X :=
      (sheafToPresheaf J (ModuleCat.{u} K)).obj B)).app V (b ⊗ₜ[K] c) := by
  change ((Monoidal.MonFunctorCategoryEquivalence.functorObjObj
    ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)) V).mon.mul).hom (b ⊗ₜ[ℤ] c) = _
  rw [pointMonoid_eq]
  rfl

private noncomputable def scalarMap (V : Cᵒᵖ) :
    K →+* (InternalAbelianSheafModule.presheafRings
      ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B))).obj V := by
  let A := (Monoidal.MonFunctorCategoryEquivalence.functorObjObj
    ((sheafToPresheaf J (ModuleCat.{u} K)).obj B) V)
  letI : MonObj A.X := A.mon
  refine { η[A.X].hom.toAddMonoidHom with map_one' := ?_, map_mul' := ?_ }
  · change η[A.X] 1 =
      ((Monoidal.MonFunctorCategoryEquivalence.functorObjObj
        ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)) V).mon.one).hom (ULift.up 1)
    rw [pointMonoid_eq]
    change η[A.X] 1 = η[A.X] ((1 : ℤ) • (1 : K))
    simp
  · intro r s
    change η[A.X] (r * s) =
      ((Monoidal.MonFunctorCategoryEquivalence.functorObjObj
        ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)) V).mon.mul).hom
          (η[A.X] r ⊗ₜ[ℤ] η[A.X] s)
    rw [pointMonoid_eq]
    have h := ConcreteCategory.congr_hom (MonObj.one_mul A.X) (r ⊗ₜ[K] η[A.X] s)
    exact (η[A.X].hom.map_smul r s).trans h.symm

private theorem scalarMap_mul (V : Cᵒᵖ) (r : K) (b : B.obj.obj V) :
    @HMul.hMul (B.obj.obj V) (B.obj.obj V) (B.obj.obj V)
      (inferInstance) (scalarMap J K B V r) b = r • b := by
  change ((Monoidal.MonFunctorCategoryEquivalence.functorObjObj
    ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)) V).mon.mul).hom
      (scalarMap J K B V r ⊗ₜ[ℤ] b) = _
  rw [pointMonoid_eq]
  exact ConcreteCategory.congr_hom
    (congr_app (MonObj.one_mul
      ((sheafToPresheaf J (ModuleCat.{u} K)).obj B)) V) (r ⊗ₜ[K] b)

private theorem mul_scalarMap (V : Cᵒᵖ) (r : K) (b : B.obj.obj V) :
    @HMul.hMul (B.obj.obj V) (B.obj.obj V) (B.obj.obj V)
      (inferInstance) b (scalarMap J K B V r) = r • b := by
  change ((Monoidal.MonFunctorCategoryEquivalence.functorObjObj
    ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)) V).mon.mul).hom
      (b ⊗ₜ[ℤ] scalarMap J K B V r) = _
  rw [pointMonoid_eq]
  exact ConcreteCategory.congr_hom
    (congr_app (MonObj.mul_one
      ((sheafToPresheaf J (ModuleCat.{u} K)).obj B)) V) (b ⊗ₜ[K] r)

private noncomputable def fullPreimage {M N : Mod (Sheaf J (ModuleCat.{u} K)) B}
    (f : ((U J K).mapMod B).obj M ⟶ ((U J K).mapMod B).obj N) : M ⟶ N := by
  let g : M.X ⟶ N.X :=
    ⟨{ app V := ModuleCat.ofHom
        ({ toFun := fun x ↦ (f.hom.hom.app V).hom x
           map_add' := fun x y ↦ map_add (f.hom.hom.app V).hom x y
           map_smul' := fun r x ↦ by
            exact (congrArg (f.hom.hom.app V).hom
              (sectionAction_one J K B M V r x)).symm.trans
                ((sectionAction_linear J K B f V _ x).trans
                  (sectionAction_one J K B N V r _)) } :
            M.X.obj.obj V →ₗ[K] N.X.obj.obj V)
       naturality V W a := by
         ext x
         exact ConcreteCategory.congr_hom (f.hom.hom.naturality a) x }⟩
  refine Mod.homMk g ?_
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro b x
  exact sectionAction_linear J K B f V b x

private noncomputable def fullyFaithful : ((U J K).mapMod B).FullyFaithful where
  preimage f := fullPreimage J K B f
  map_preimage f := by apply Mod.hom_ext; ext V x; rfl
  preimage_map f := by apply Mod.hom_ext; ext V x; rfl

private noncomputable abbrev ordinary (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :=
  InternalAbelianSheafModule.presheafModules
    ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B))
      (((sheafToPresheaf J Ab.{u}).mapMod ((U J K).obj B)).obj M)

private noncomputable def recoveredPresheaf
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) : Cᵒᵖ ⥤ ModuleCat.{u} K where
  obj V := by
    letI := Module.compHom ((ordinary J K B M).obj V) (scalarMap J K B V)
    exact ModuleCat.of K ((ordinary J K B M).obj V)
  map {V W} f := by
    letI := Module.compHom ((ordinary J K B M).obj V) (scalarMap J K B V)
    letI := Module.compHom ((ordinary J K B M).obj W) (scalarMap J K B W)
    refine ModuleCat.ofHom
      { ((ordinary J K B M).map f).hom.toAddMonoidHom with map_smul' := ?_ }
    intro r x
    change (ordinary J K B M).map f ((scalarMap J K B V r) • x) =
      (scalarMap J K B W r) • (ordinary J K B M).map f x
    rw [(ordinary J K B M).map_smul]
    congr 1
    exact (ConcreteCategory.congr_hom
      ((MonObj.one (X := (sheafToPresheaf J (ModuleCat.{u} K)).obj B)).naturality f) r).symm
  map_id V := by
    ext x
    change (ordinary J K B M).map (𝟙 V) x = x
    rw [(ordinary J K B M).map_id]
    rfl
  map_comp f g := by
    ext x
    change (ordinary J K B M).map (f ≫ g) x =
      (ordinary J K B M).map g ((ordinary J K B M).map f x)
    rw [(ordinary J K B M).map_comp]
    rfl

private noncomputable def recoveredSheaf
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) : Sheaf J (ModuleCat.{u} K) := by
  refine ⟨recoveredPresheaf J K B M, ?_⟩
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{u} K) Ab.{u})
  change Presheaf.IsSheaf J M.X.obj
  exact M.X.property

private noncomputable def recoveredPresheafAction
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :
    ((sheafToPresheaf J (ModuleCat.{u} K)).obj B) ⊗
      (recoveredSheaf J K B M).obj ⟶ (recoveredSheaf J K B M).obj where
  app V := by
    let P := ordinary J K B M
    let A := ((sheafToPresheaf J (ModuleCat.{u} K)).obj B).obj V
    let X := (recoveredSheaf J K B M).obj.obj V
    let : Ring A := sectionRing J K B V
    let : Module A X := (P.obj V).isModule
    letI : Module K X := Module.compHom (P.obj V) (scalarMap J K B V)
    letI : Module K (P.obj V) := Module.compHom (P.obj V) (scalarMap J K B V)
    letI : Module
        ((InternalAbelianSheafModule.presheafRings
          ((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B))).obj V) X :=
      (P.obj V).isModule
    let f : A →ₗ[K] X →ₗ[K] X := LinearMap.mk₂ K
      (fun b x ↦ b • x)
      (fun b c x ↦ add_smul b c x)
      (fun r b x ↦ by
        change (r • b) • x = (scalarMap J K B V r : A) • (b • x)
        rw [← mul_smul, scalarMap_mul])
      (fun b x y ↦ smul_add b x y)
      (fun r b x ↦ by
        change b • ((scalarMap J K B V r : A) • x) =
          (scalarMap J K B V r : A) • (b • x)
        rw [← mul_smul, ← mul_smul, scalarMap_mul, mul_scalarMap])
    exact ModuleCat.ofHom (TensorProduct.lift f)
  naturality V W f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro b x
    exact ((ordinary J K B M).map_smul f b x).symm

private noncomputable def recoveredPresheafModule
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :
    Mod (Cᵒᵖ ⥤ ModuleCat.{u} K)
      ((sheafToPresheaf J (ModuleCat.{u} K)).obj B) := by
  letI : ModObj ((sheafToPresheaf J (ModuleCat.{u} K)).obj B)
      (recoveredSheaf J K B M).obj := ModObj.mk' _ (recoveredPresheafAction J K B M)
        (by
          apply NatTrans.ext
          funext V
          apply ModuleCat.hom_ext
          apply TensorProduct.ext'
          intro r x
          rfl)
        (by
          apply NatTrans.ext
          funext V
          apply ModuleCat.hom_ext
          apply TensorProduct.ext_threefold
          intro b c x
          let P := ordinary J K B M
          let A := ((sheafToPresheaf J (ModuleCat.{u} K)).obj B).obj V
          let X := (recoveredSheaf J K B M).obj.obj V
          let : Ring A := sectionRing J K B V
          let : Module A X := (P.obj V).isModule
          change ((MonObj.mul (X :=
            (sheafToPresheaf J (ModuleCat.{u} K)).obj B)).app V (b ⊗ₜ[K] c)) • x =
              b • (c • (x : P.obj V))
          rw [← sectionRing_mul]
          exact mul_smul b c x)
  exact ⟨(recoveredSheaf J K B M).obj⟩

private noncomputable def recoveredModule
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) : Mod (Sheaf J (ModuleCat.{u} K)) B := by
  let adj := sheafificationAdjunction J (ModuleCat.{u} K)
  let ψ := (adj.homEquiv _ _).symm
    (𝟙 ((sheafToPresheaf J (ModuleCat.{u} K)).obj B))
  have hψ : ψ = adj.counit.app B := by simp [ψ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by rw [hψ]; infer_instance
  exact (adj.modLeft (𝟙 ((sheafToPresheaf J (ModuleCat.{u} K)).obj B))).obj
    (recoveredPresheafModule J K B M)

private noncomputable def recoveredPresheafUnit
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :
    recoveredPresheafModule J K B M ⟶
      ((sheafToPresheaf J (ModuleCat.{u} K)).mapMod B).obj
        (recoveredModule J K B M) := by
  let adj := sheafificationAdjunction J (ModuleCat.{u} K)
  let ψ := (adj.homEquiv _ _).symm
    (𝟙 ((sheafToPresheaf J (ModuleCat.{u} K)).obj B))
  have hψ : ψ = adj.counit.app B := by simp [ψ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by rw [hψ]; infer_instance
  exact (adj.modAdjunction
    (𝟙 ((sheafToPresheaf J (ModuleCat.{u} K)).obj B))).unit.app _ ≫
      (Mod.comapId _).hom.app _

private theorem recoveredPresheafUnit_hom
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :
    (recoveredPresheafUnit J K B M).hom =
      toSheafify J (recoveredPresheaf J K B M) := by
  let adj := sheafificationAdjunction J (ModuleCat.{u} K)
  let ψ := (adj.homEquiv _ _).symm
    (𝟙 ((sheafToPresheaf J (ModuleCat.{u} K)).obj B))
  have hψ : ψ = adj.counit.app B := by simp [ψ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by rw [hψ]; infer_instance
  dsimp only [recoveredPresheafUnit]
  change (((sheafificationAdjunction J (ModuleCat.{u} K)).modAdjunction
    (𝟙 ((sheafToPresheaf J (ModuleCat.{u} K)).obj B))).unit.app
      (recoveredPresheafModule J K B M)).hom ≫ 𝟙 _ = _
  rw [Category.comp_id, Adjunction.modAdjunction_unit_app_hom]
  rfl

private noncomputable def recoveredAbUnit
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :
    M.X ⟶ (U J K).obj (recoveredModule J K B M).X := by
  let adj := sheafificationAdjunction J (ModuleCat.{u} K)
  let e := adj.unit.app (recoveredPresheaf J K B M)
  exact ⟨{ app V := (forget₂ (ModuleCat.{u} K) Ab.{u}).map (e.app V)
           naturality V W f := by
             ext x
             exact ConcreteCategory.congr_hom (e.naturality f) x }⟩

private theorem recoveredAbUnit_isIso
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :
    IsIso (recoveredAbUnit J K B M) := by
  let adj := sheafificationAdjunction J (ModuleCat.{u} K)
  have : IsIso (adj.unit.app (recoveredSheaf J K B M).obj) :=
    isIso_toSheafify J (recoveredSheaf J K B M).property
  have (V : Cᵒᵖ) : IsIso ((recoveredAbUnit J K B M).hom.app V) :=
    inferInstanceAs (IsIso ((forget₂ (ModuleCat.{u} K) Ab.{u}).map
      ((adj.unit.app (recoveredSheaf J K B M).obj).app V)))
  have : IsIso (recoveredAbUnit J K B M).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf J Ab.{u}).map (recoveredAbUnit J K B M)) :=
    inferInstanceAs (IsIso (recoveredAbUnit J K B M).hom)
  exact isIso_of_reflects_iso _ (sheafToPresheaf J Ab.{u})

private noncomputable def recoveredUnit
    (M : Mod (Sheaf J Ab.{u}) ((U J K).obj B)) :
    M ⟶ ((U J K).mapMod B).obj (recoveredModule J K B M) := by
  refine Mod.homMk (recoveredAbUnit J K B M) ?_
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro b x
  change (recoveredAbUnit J K B M).hom.app V
      (((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u}) ((U J K).obj B) M.X ≫
        (sheafToPresheaf J Ab.{u}).map (Mod.act M.X)).app V) (b ⊗ₜ[ℤ] x)) =
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u}) ((U J K).obj B)
        ((U J K).obj (recoveredModule J K B M).X) ≫
      (sheafToPresheaf J Ab.{u}).map
        (Mod.act (((U J K).mapMod B).obj (recoveredModule J K B M)).X)).app V)
      (b ⊗ₜ[ℤ] ((recoveredAbUnit J K B M).hom.app V) x))
  rw [sectionAction_forget (M := recoveredModule J K B M)]
  let : Module K (((sheafToPresheaf J Ab.{u}).obj ((U J K).obj B)).obj V) :=
    (B.obj.obj V).isModule
  let : Module K (((sheafToPresheaf J Ab.{u}).obj M.X).obj V) :=
    ((recoveredPresheaf J K B M).obj V).isModule
  have hj := ConcreteCategory.congr_hom
    (congr_app (Mod.act_hom (recoveredPresheafUnit J K B M)) V)
      ((b : B.obj.obj V) ⊗ₜ[K] (x : (recoveredPresheaf J K B M).obj V))
  rw [recoveredPresheafUnit_hom] at hj
  exact hj

private theorem forgetting_isEquivalence : ((U J K).mapMod B).IsEquivalence := by
  let := (fullyFaithful J K B).full
  let := (fullyFaithful J K B).faithful
  let : ((U J K).mapMod B).EssSurj := ⟨fun M ↦ by
    have := recoveredAbUnit_isIso J K B M
    have : IsIso ((Mod.forget ((U J K).obj B)).map (recoveredUnit J K B M)) :=
      inferInstanceAs (IsIso (recoveredAbUnit J K B M))
    have : IsIso (recoveredUnit J K B M) :=
      isIso_of_reflects_iso _ (Mod.forget ((U J K).obj B))
    exact ⟨recoveredModule J K B M, ⟨(asIso (recoveredUnit J K B M)).symm⟩⟩⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end CategoryTheory.ScalarForgetting

namespace AlgebraicGeometry.ProEtale

/-- Forgetting the ambient vector-space structure of a native module loses no data: the
forgetful functor `AdicSheaf.forgetAb ℓ T` is an equivalence. -/
theorem nativeScalarForgetting_isEquivalence (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    (AdicSheaf.forgetAb ℓ T).IsEquivalence := by
  exact CategoryTheory.ScalarForgetting.forgetting_isEquivalence
    (Scheme.ProEt.topology T) (ULift.{u + 1} (PadicAlgCl ℓ)) (adicConstantSheaf ℓ T)

end AlgebraicGeometry.ProEtale
