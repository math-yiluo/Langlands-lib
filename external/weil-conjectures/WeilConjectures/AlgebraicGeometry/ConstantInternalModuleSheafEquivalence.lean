/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence

/-! # Encoding internal modules over a constant ring sheaf

Source: Bhatt--Scholze, Section 5.3, and Stacks Project, Tag 093I;
the tensor and sheafification encoding argument is expanded below
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

namespace ConstantInternalModuleSheafEncoding

section PresheafEncoding

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R]

local instance evaluationMonoidal (U : C) : ((evaluation C Ab.{w}).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

abbrev A : C ⥤ Ab.{w} :=
  (Functor.const C).obj (RingCat.of R) ⋙ forget₂ RingCat.{w} Ab.{w}

noncomputable def presheafToFunctor : CategoryTheory.Mod (C ⥤ Ab.{w}) (A (C := C) R) ⥤
    (C ⥤ CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R)) where
  obj M :=
    { obj U := (((evaluation C Ab.{w}).obj U).mapMod (A (C := C) R)).obj M
      map f := CategoryTheory.Mod.homMk (M.X.map f) (by
        exact ((CategoryTheory.Mod.act (A := A (C := C) R) M.X).naturality f).symm)
      map_id U := CategoryTheory.Mod.hom_ext _ _ (M.X.map_id U)
      map_comp f g := CategoryTheory.Mod.hom_ext _ _ (M.X.map_comp f g) }
  map φ :=
    { app U := CategoryTheory.Mod.homMk (φ.hom.app U) (by
        exact congr_app (CategoryTheory.Mod.act_hom φ) U)
      naturality _ _ f := CategoryTheory.Mod.hom_ext _ _ (φ.hom.naturality f) }
  map_id M := by ext U; rfl
  map_comp φ ψ := by ext U; rfl

noncomputable def functorToPresheafObj
    (F : C ⥤ CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R)) :
    CategoryTheory.Mod (C ⥤ Ab.{w}) (A (C := C) R) := by
  let X := F ⋙ CategoryTheory.Mod.forget (AddCommGrpCat.of R)
  let act : A (C := C) R ⊗ X ⟶ X :=
    { app U := γ[AddCommGrpCat.of R,(F.obj U).X]
      naturality _ _ f := by exact (CategoryTheory.Mod.act_hom (F.map f)).symm }
  letI : ModObj (A (C := C) R) X := ModObj.mk' (A (C := C) R) act
    (NatTrans.ext (funext fun U ↦ ModObj.one_smul_self (AddCommGrpCat.of R) (F.obj U).X))
    (NatTrans.ext (funext fun U ↦ ModObj.mul_smul_self (AddCommGrpCat.of R) (F.obj U).X))
  exact ⟨X⟩

noncomputable def preimageMap {M N : CategoryTheory.Mod (C ⥤ Ab.{w}) (A (C := C) R)}
    (φ : (presheafToFunctor R).obj M ⟶ (presheafToFunctor R).obj N) : M ⟶ N :=
  CategoryTheory.Mod.homMk
    { app U := (φ.app U).hom
      naturality _ _ f := congrArg CategoryTheory.Mod.Hom.hom (φ.naturality f) }
    (NatTrans.ext (funext fun U ↦ CategoryTheory.Mod.act_hom (φ.app U)))

noncomputable def presheafToFunctorFullyFaithful :
    (presheafToFunctor (C := C) R).FullyFaithful where
  preimage φ := preimageMap R φ
  map_preimage φ := by ext U; rfl
  preimage_map φ := CategoryTheory.Mod.hom_ext _ _ (by ext U; rfl)

noncomputable def realizationIso (F : C ⥤ CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R)) :
    (presheafToFunctor R).obj (functorToPresheafObj R F) ≅ F :=
  NatIso.ofComponents (fun U ↦ CategoryTheory.Mod.isoMk (Iso.refl _) (by simp))
    (fun _ ↦ CategoryTheory.Mod.hom_ext _ _ rfl)

end PresheafEncoding

section ModuleLocalization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (A : Cᵒᵖ ⥤ Ab.{w}) [MonObj A]

noncomputable abbrev moduleLocalizationAdjunction :=
  (sheafificationAdjunction J Ab.{w}).mapModAdjunction A

noncomputable abbrev moduleLocalizationRight :=
  (sheafificationAdjunction J Ab.{w}).modRight
    ((sheafificationAdjunction J Ab.{w}).unit.app A)

noncomputable def moduleLocalizationRightFullyFaithful :
    (moduleLocalizationRight J A).FullyFaithful := by
  let adj := moduleLocalizationAdjunction J A
  have : ∀ N, IsIso (adj.counit.app N) := by
    intro N
    rw [← isIso_iff_of_reflects_iso _ (CategoryTheory.Mod.forget _)]
    change IsIso ((adj.counit.app N).hom)
    rw [Adjunction.mapModAdjunction_counit_app_hom]
    infer_instance
  have : IsIso adj.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun N ↦ inferInstance
  exact adj.fullyFaithfulROfIsIsoCounit

end ModuleLocalization

section SheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

noncomputable def modulePresheafEncoding
    (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R) :=
  presheafToFunctor (C := Cᵒᵖ) R ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj G

lemma modulePresheafEncoding_forget
    (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R)
    (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = CategoryTheory.Mod.forget (AddCommGrpCat.of R)) :
    modulePresheafEncoding (C := C) R G ⋙
      (Functor.whiskeringRight Cᵒᵖ _ _).obj (forget₂ (ModuleCat.{w} R) Ab.{w}) =
        CategoryTheory.Mod.forget (A (C := Cᵒᵖ) R) := by
  change presheafToFunctor R ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w}) = _
  rw [hG]
  rfl

instance presheafToFunctorIsEquivalence :
    (presheafToFunctor (C := Cᵒᵖ) R).IsEquivalence where
  faithful := (presheafToFunctorFullyFaithful R).faithful
  full := (presheafToFunctorFullyFaithful R).full
  essSurj := ⟨fun F ↦ ⟨functorToPresheafObj R F, ⟨realizationIso R F⟩⟩⟩

noncomputable def sheafEncoding
    (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R)
    (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = CategoryTheory.Mod.forget (AddCommGrpCat.of R))
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
    [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})] :
    CategoryTheory.Mod (Sheaf J Ab.{w}) ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) ⥤
      Sheaf J (ModuleCat.{w} R) where
  obj N := by
    let P := modulePresheafEncoding (C := C) R G
    let Q := moduleLocalizationRight J (A (C := Cᵒᵖ) R)
    refine ⟨P.obj (Q.obj N), ?_⟩
    apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{w} R) Ab.{w})
    have h := congrArg (fun F ↦ F.obj (Q.obj N)) (modulePresheafEncoding_forget (C := C) R G hG)
    change (P.obj (Q.obj N)) ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = N.X.obj at h
    rw [h]
    exact N.X.property
  map φ := ⟨(modulePresheafEncoding (C := C) R G).map
    ((moduleLocalizationRight J (A (C := Cᵒᵖ) R)).map φ)⟩
  map_id N := by
    apply (sheafToPresheaf J (ModuleCat.{w} R)).map_injective
    exact ((moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙
      modulePresheafEncoding (C := C) R G).map_id N)
  map_comp φ ψ := by
    apply (sheafToPresheaf J (ModuleCat.{w} R)).map_injective
    exact ((moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙
      modulePresheafEncoding (C := C) R G).map_comp φ ψ)

variable (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = CategoryTheory.Mod.forget (AddCommGrpCat.of R))
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
    [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]

instance localizationRightFull :
    (moduleLocalizationRight J (A (C := Cᵒᵖ) R)).Full :=
  (moduleLocalizationRightFullyFaithful J _).full

instance localizationRightFaithful :
    (moduleLocalizationRight J (A (C := Cᵒᵖ) R)).Faithful :=
  (moduleLocalizationRightFullyFaithful J _).faithful

instance moduleEncodingIsEquivalence :
    (modulePresheafEncoding (C := C) R G).IsEquivalence := by
  unfold modulePresheafEncoding
  infer_instance

instance sheafEncodingFull : (sheafEncoding J R G hG).Full := by
  have : (modulePresheafEncoding (C := C) R G).Full :=
    (moduleEncodingIsEquivalence R G).full
  have : (moduleLocalizationRight J (A (C := Cᵒᵖ) R)).Full :=
    (moduleLocalizationRightFullyFaithful J _).full
  exact Functor.Full.of_comp_faithful_iso
    (G := sheafToPresheaf J (ModuleCat.{w} R))
    (H := moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙ modulePresheafEncoding (C := C) R G)
    (Iso.refl _)

instance sheafEncodingFaithful : (sheafEncoding J R G hG).Faithful := by
  have : (modulePresheafEncoding (C := C) R G).Faithful :=
    (moduleEncodingIsEquivalence R G).faithful
  have : (moduleLocalizationRight J (A (C := Cᵒᵖ) R)).Faithful :=
    (moduleLocalizationRightFullyFaithful J _).faithful
  exact Functor.Faithful.of_comp_iso
    (G := sheafToPresheaf J (ModuleCat.{w} R))
    (H := moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙ modulePresheafEncoding (C := C) R G)
    (Iso.refl _)

instance sheafEncodingEssSurj : (sheafEncoding J R G hG).EssSurj where
  mem_essImage N := by
    let P := modulePresheafEncoding (C := C) R G
    let M := P.objPreimage N.obj
    let e := P.objObjPreimageIso N.obj
    have hM : Presheaf.IsSheaf J M.X := by
      have hME : P.obj M ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = M.X :=
        congrArg (fun F ↦ F.obj M) (modulePresheafEncoding_forget (C := C) R G hG)
      let e' := (eqToIso hME).symm ≪≫
        ((Functor.whiskeringRight Cᵒᵖ _ _).obj
          (forget₂ (ModuleCat.{w} R) Ab.{w})).mapIso e
      exact (Presheaf.isSheaf_of_iso_iff e').mpr
        ((sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).obj N).property
    let adj := moduleLocalizationAdjunction J (A (C := Cᵒᵖ) R)
    have hη : IsIso (adj.unit.app M) := by
      rw [← isIso_iff_of_reflects_iso _ (CategoryTheory.Mod.forget _)]
      change IsIso ((adj.unit.app M).hom)
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      exact isIso_toSheafify J hM
    exact ⟨_, ⟨ObjectProperty.isoMk _ ((P.mapIso (asIso (adj.unit.app M))).symm ≪≫ e)⟩⟩

instance sheafEncodingIsEquivalence : (sheafEncoding J R G hG).IsEquivalence where

end SheafEncoding

end ConstantInternalModuleSheafEncoding

section SheafEncoding

open ConstantInternalModuleSheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
  [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

end SheafEncoding

end CategoryTheory
