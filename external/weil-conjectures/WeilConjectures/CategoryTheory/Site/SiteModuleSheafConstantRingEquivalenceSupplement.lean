/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence

/-! # Constant-coefficient module sheaves on an arbitrary small site

Source: Stacks Project, Modules on Sites, Tag 093I, and Cohomology on Sites,
Tag 03FD; encoding construction used by Tag 094G
(blueprint: lem-weil-pbc-site-module-sheaf-constant-ring-equivalence).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{u} C]
-- Constant-ring module presheaves encode exactly ModuleCat-valued presheaves.
private noncomputable def constantModulePresheaf
    (_J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (Cᵒᵖ ⥤ ModuleCat.{u} Λ) ⥤
      PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map φ :=
    { app := φ.app
      naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }

private noncomputable def constantModuleFullyFaithful
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (constantModulePresheaf J Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable instance (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (constantModulePresheaf J Λ).Full := (constantModuleFullyFaithful J Λ).full

private noncomputable instance (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (constantModulePresheaf J Λ).Faithful := (constantModuleFullyFaithful J Λ).faithful

private noncomputable def moduleEmbedding (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :=
  sheafToPresheaf J (ModuleCat.{u} Λ) ⋙ constantModulePresheaf J Λ

private noncomputable instance (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (moduleEmbedding J Λ).Full :=
  inferInstanceAs (sheafToPresheaf J (ModuleCat.{u} Λ) ⋙
    constantModulePresheaf J Λ).Full

private noncomputable instance (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (moduleEmbedding J Λ).Faithful :=
  inferInstanceAs (sheafToPresheaf J (ModuleCat.{u} Λ) ⋙
    constantModulePresheaf J Λ).Faithful

private noncomputable def moduleExtension (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :=
  moduleEmbedding J Λ ⋙ PresheafOfModules.sheafification.{u} α

private noncomputable def moduleExtensionForgetIso
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    moduleExtension J Λ R α ⋙ SheafOfModules.toSheaf R ≅
      sheafCompose J
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun F ↦ asIso ((sheafificationAdjunction
    J AddCommGrpCat.{u}).counit.app
      ((sheafCompose J
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)))
    (fun φ ↦ (sheafificationAdjunction J AddCommGrpCat.{u}).counit.naturality
      ((sheafCompose J
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map φ))

-- The module-sheafification unit is invertible on objects already satisfying descent.

private noncomputable instance moduleEmbeddingUnitIsIso
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (F : Sheaf J (ModuleCat.{u} Λ)) :
    IsIso ((PresheafOfModules.sheafificationAdjunction.{u} α).unit.app
      ((moduleEmbedding J Λ).obj F)) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  apply isIso_toSheafify
  exact ((sheafCompose J
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F).property

private noncomputable def moduleEmbeddingUnitIso
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    moduleEmbedding J Λ ≅ moduleExtension J Λ R α ⋙
      (SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars α) := by
  let η := Functor.whiskerLeft (moduleEmbedding J Λ)
    (PresheafOfModules.sheafificationAdjunction.{u} α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    exact moduleEmbeddingUnitIsIso J Λ R α F
  exact asIso η

private noncomputable instance (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    (moduleExtension J Λ R α).Faithful :=
  Functor.Faithful.of_comp_iso (moduleEmbeddingUnitIso J Λ R α).symm

private noncomputable instance (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    (moduleExtension J Λ R α).Full :=
  Functor.Full.of_comp_faithful_iso (moduleEmbeddingUnitIso J Λ R α).symm

-- Restriction of scalars retains the additive sheaf and supplies essential surjectivity.
private noncomputable def moduleRestrictionObj
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (M : SheafOfModules.{u} R) :
    Sheaf J (ModuleCat.{u} Λ) := by
  let P := (PresheafOfModules.restrictScalars α).obj M.val
  let F : Cᵒᵖ ⥤ ModuleCat.{u} Λ :=
    { obj := P.obj
      map f := P.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
  exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) M.isSheaf⟩

private noncomputable def moduleRestriction
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    SheafOfModules.{u} R ⥤ Sheaf J (ModuleCat.{u} Λ) where
  obj := moduleRestrictionObj J Λ R α
  map φ := ⟨{
    app X := (PresheafOfModules.restrictScalars α).map φ.val |>.app X
    naturality _ _ f := by
      ext x
      exact PresheafOfModules.naturality_apply
        ((PresheafOfModules.restrictScalars α).map φ.val) f x }⟩

private noncomputable instance (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    (moduleExtension J Λ R α).EssSurj where
  mem_essImage M := by
    refine ⟨moduleRestrictionObj J Λ R α M, ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction.{u} α).counit.app M)

private noncomputable def constantExtensionUnit
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ ⋙
      PresheafOfModules.sheafification.{u} α ⟶
    constantSheaf J (ModuleCat.{u} Λ) ⋙ moduleExtension J Λ R α :=
  Functor.whiskerRight (Functor.whiskerRight
    (Functor.whiskerLeft (Functor.const Cᵒᵖ)
      (sheafificationAdjunction J (ModuleCat.{u} Λ)).unit)
        (constantModulePresheaf J Λ))
    (PresheafOfModules.sheafification.{u} α)

private theorem constantExtensionUnit_isIso
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    IsIso (constantExtensionUnit J Λ R α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hw : (J.W.inverseImage (PresheafOfModules.toPresheaf.{u} _))
      ((constantModulePresheaf J Λ).map
        (toSheafify J ((Functor.const Cᵒᵖ).obj M))) := by
    change J.W (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
    have : Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})) := by
      apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
      change Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget (ModuleCat.{u} Λ)))
      infer_instance
    have : Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})) := by
      apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
      change Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget (ModuleCat.{u} Λ)))
      infer_instance
    exact J.W_of_isLocallyBijective _
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms.{u, u, u, u}
    α] at hw
  exact hw

private noncomputable def restrictConstantUnit
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (U : C) (M : ModuleCat.{u} Λ) :
    (SheafOfModules.strictPerfectConstantPresheaf (C := Over U) Λ).obj M ⟶
      (PresheafOfModules.restrictScalars (Functor.whiskerLeft (Over.forget U).op α)).obj
        ((SheafOfModules.overFunctor R U).obj
          ((PresheafOfModules.sheafification.{u} α).obj
            ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).obj M))).val := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u} α).unit.app
    ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).obj M)
  exact
    { app X := η.app ((Over.forget U).op.obj X)
      naturality {X Y} f := by
        ext x
        exact PresheafOfModules.naturality_apply η ((Over.forget U).op.map f) x }

private noncomputable def constantSliceTransformation
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (U : C) :
    let αU := Functor.whiskerLeft (Over.forget U).op α
    letI : Presheaf.IsLocallyInjective (J.over U) αU :=
      Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α
    letI : Presheaf.IsLocallySurjective (J.over U) αU :=
      Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α
    SheafOfModules.strictPerfectConstantPresheaf (C := Over U) Λ ⋙
        PresheafOfModules.sheafification.{u} (R := R.over U) αU ⟶
      SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ ⋙
        PresheafOfModules.sheafification.{u} α ⋙ SheafOfModules.overFunctor R U := by
  let : Presheaf.IsLocallyInjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op α) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α
  let : Presheaf.IsLocallySurjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op α) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α
  dsimp only
  refine
    { app M := (PresheafOfModules.sheafificationHomEquiv.{u}
      (R := R.over U)
      (P := (SheafOfModules.strictPerfectConstantPresheaf (C := Over U) Λ).obj M)
      (F := (SheafOfModules.overFunctor R U).obj
        ((PresheafOfModules.sheafification.{u} α).obj
          ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).obj M)))
      (Functor.whiskerLeft (Over.forget U).op α)).symm
          (restrictConstantUnit J Λ R α U M)
      naturality := ?_ }
  intro M N f
  apply ((PresheafOfModules.sheafificationAdjunction.{u} (R := R.over U)
    (Functor.whiskerLeft (Over.forget U).op α)).homEquiv
      ((SheafOfModules.strictPerfectConstantPresheaf (C := Over U) Λ).obj M)
      ((SheafOfModules.overFunctor R U).obj
        ((PresheafOfModules.sheafification.{u} α).obj
          ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).obj N)))).injective
  simp only [Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    Equiv.apply_symm_apply]
  erw [Equiv.apply_symm_apply]
  ext X x
  exact congrArg (fun k ↦ (k.app ((Over.forget U).op.obj X)).hom x)
    ((PresheafOfModules.sheafificationAdjunction.{u} α).unit.naturality
      ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).map f))

private theorem constantSliceTransformation_isIso
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (U : C) :
    IsIso (constantSliceTransformation J Λ R α U) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let : Presheaf.IsLocallyInjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op α) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α
  let : Presheaf.IsLocallySurjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op α) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α
  let g := restrictConstantUnit J Λ R α U M
  let ψ : (PresheafOfModules.sheafification.{u} (R := R.over U)
      (Functor.whiskerLeft (Over.forget U).op α)).obj
        ((SheafOfModules.strictPerfectConstantPresheaf (C := Over U) Λ).obj M) ⟶
      (SheafOfModules.overFunctor R U).obj
        ((PresheafOfModules.sheafification.{u} α).obj
          ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).obj M)) :=
    (PresheafOfModules.sheafificationHomEquiv.{u}
      (R := R.over U)
      (P := (SheafOfModules.strictPerfectConstantPresheaf (C := Over U) Λ).obj M)
      (F := (SheafOfModules.overFunctor R U).obj
        ((PresheafOfModules.sheafification.{u} α).obj
          ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).obj M)))
      (Functor.whiskerLeft (Over.forget U).op α)).symm g
  have hg : (J.over U).W
      ((PresheafOfModules.toPresheaf.{u} _).map g) := by
    change (J.over U).W (Functor.whiskerLeft (Over.forget U).op
      (toSheafify J ((Functor.const Cᵒᵖ).obj ((forget₂ _ AddCommGrpCat.{u}).obj M))))
    have : Presheaf.IsLocallyInjective (J.over U)
        (Functor.whiskerLeft (Over.forget U).op
          (toSheafify J ((Functor.const Cᵒᵖ).obj ((forget₂ _ AddCommGrpCat.{u}).obj M)))) :=
      Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
    have : Presheaf.IsLocallySurjective (J.over U)
        (Functor.whiskerLeft (Over.forget U).op
          (toSheafify J ((Functor.const Cᵒᵖ).obj ((forget₂ _ AddCommGrpCat.{u}).obj M)))) :=
      Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
    exact (J.over U).W_of_isLocallyBijective _
  have : IsIso ψ := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{u} (R.over U))]
    dsimp only [ψ]
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
      Adjunction.homEquiv_counit]
    have : IsIso ((presheafToSheaf (J.over U) AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf.{u} _).map g)) := by
      rw [(J.over U).W_eq_inverseImage_isomorphisms] at hg
      exact hg
    exact IsIso.comp_isIso' this
      (isIso_sheafificationAdjunction_counit
        (J := J.over U) (D := AddCommGrpCat.{u})
        ((SheafOfModules.toSheaf (R.over U)).obj
          ((SheafOfModules.overFunctor R U).obj
            ((PresheafOfModules.sheafification.{u} α).obj
              ((SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ).obj M)))))
  exact this

private noncomputable def moduleRestrictionCounit
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    moduleRestriction J Λ R α ⋙ moduleExtension J Λ R α ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ asIso ((PresheafOfModules.sheafificationAdjunction.{u} α).counit.app M))
    (fun φ ↦ (PresheafOfModules.sheafificationAdjunction.{u} α).counit.naturality φ)

private noncomputable instance moduleRestriction_isEquivalence
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    (moduleRestriction J Λ R α).IsEquivalence := by
  let : (moduleExtension J Λ R α).IsEquivalence := {}
  let : (moduleRestriction J Λ R α ⋙ moduleExtension J Λ R α).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleRestrictionCounit J Λ R α).symm
  exact Functor.isEquivalence_of_comp_right _ (moduleExtension J Λ R α)

private noncomputable def moduleRestrictionUnit
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    moduleExtension J Λ R α ⋙ moduleRestriction J Λ R α ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (moduleExtension J Λ R α)
    ((Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (moduleRestrictionCounit J Λ R α) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

private noncomputable def moduleRestrictionConstantIso
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ ⋙
      PresheafOfModules.sheafification.{u} α ⋙ moduleRestriction J Λ R α ≅
        constantSheaf J (ModuleCat.{u} Λ) := by
  have := constantExtensionUnit_isIso J Λ R α
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (constantExtensionUnit J Λ R α)) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (moduleRestrictionUnit J Λ R α) ≪≫
    Functor.rightUnitor _

/-- Module-valued sheaves are modules over the constant ring sheaf. The equivalence
retains the additive sheaf and naturally identifies both constant-module realizations.
The locally bijective constant-ring unit may be the restriction of a global unit to a slice.

Source: Stacks Project, Modules on Sites, Tag 093I (constant algebraic structures),
and Cohomology on Sites, Tag 03FD; the encoding used by Tag 094G.
(blueprint: lem-weil-pbc-site-module-sheaf-constant-ring-equivalence).

Proof: Encode a ModuleCat-valued presheaf as modules over the constant ring presheaf,
then sheafify along the given ring unit. Local bijectivity is supplied as an explicit
instance. This includes
the usual constant commutative-ring sheafification unit after forgetting commutativity,
and its restrictions to slice sites.
On a module-valued sheaf the module-sheafification unit is invertible: its underlying
additive map is the sheafification unit of an already sheafy presheaf. Thus the encoded
embedding followed by sheafification is fully faithful. Conversely restrict any module
sheaf's scalar action along the ring unit. Its additive sheaf is unchanged, so this is
a ModuleCat-valued sheaf. The sheafification counit identifies its extension with the
original module sheaf, proving essential surjectivity. The counit on additive sheaves
gives the first natural isomorphism. For the second, start with the sheafification
unit of a constant ModuleCat-valued presheaf, encode it, and module-sheafify. Its
underlying additive map is locally bijective, so its module sheafification is invertible.
Naturality is inherited from the original unit and both functors. These arguments
include the empty site and the zero ring and require neither points nor Noetherianity.
Finally restrict the module-sheafification unit to a slice. The resulting presheaf map
has locally bijective underlying additive map. Its adjoint is invertible: after forgetting
modules it is the sheafification of that locally bijective map followed by the counit
on an additive sheaf. Naturality follows from naturality of the original module unit,
so these isomorphisms give a natural comparison of constant realizations on slices. -/
theorem site_moduleSheaf_constantRing_equivalence
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    let c := SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ ⋙
      PresheafOfModules.sheafification.{u} α
    ∃ e : Sheaf J (ModuleCat.{u} Λ) ≌ SheafOfModules.{u} R,
      Nonempty (e.functor ⋙ SheafOfModules.toSheaf R ≅
        sheafCompose J (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})) ∧
      Nonempty (c ≅ constantSheaf J (ModuleCat.{u} Λ) ⋙ e.functor) ∧
      ∀ U : C,
        let αU := Functor.whiskerLeft (Over.forget U).op α
        letI : Presheaf.IsLocallyInjective (J.over U) αU :=
          Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α
        letI : Presheaf.IsLocallySurjective (J.over U) αU :=
          Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α
        Nonempty
          (SheafOfModules.strictPerfectConstantPresheaf (C := Over U) Λ ⋙
              PresheafOfModules.sheafification.{u} (R := R.over U) αU ≅
            c ⋙ SheafOfModules.overFunctor R U) := by
  let : (moduleExtension J Λ R α).IsEquivalence := {}
  have := constantExtensionUnit_isIso J Λ R α
  refine ⟨(moduleExtension J Λ R α).asEquivalence,
    ⟨moduleExtensionForgetIso J Λ R α⟩, ⟨asIso (constantExtensionUnit J Λ R α)⟩, ?_⟩
  intro U
  have := constantSliceTransformation_isIso J Λ R α U
  exact ⟨asIso (constantSliceTransformation J Λ R α U)⟩

end CategoryTheory
