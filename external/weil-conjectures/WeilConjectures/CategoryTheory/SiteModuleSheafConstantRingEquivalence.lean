/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Constant-coefficient module sheaves on an arbitrary small site

Source: Stacks Project, Modules on Sites, Tag 093I, and Cohomology on Sites,
Tag 03FD; encoding construction used by Tag 094G
(auxiliary; not a blueprint node).
-/

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

private noncomputable instance siteModuleSheafConstantRingEquivalenceInst1
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (constantModulePresheaf J Λ).Full := (constantModuleFullyFaithful J Λ).full

private noncomputable instance siteModuleSheafConstantRingEquivalenceInst2
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (constantModulePresheaf J Λ).Faithful := (constantModuleFullyFaithful J Λ).faithful

private noncomputable def moduleEmbedding (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :=
  sheafToPresheaf J (ModuleCat.{u} Λ) ⋙ constantModulePresheaf J Λ

private noncomputable instance siteModuleSheafConstantRingEquivalenceInst3
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (moduleEmbedding J Λ).Full :=
  inferInstanceAs (sheafToPresheaf J (ModuleCat.{u} Λ) ⋙
    constantModulePresheaf J Λ).Full

private noncomputable instance siteModuleSheafConstantRingEquivalenceInst4
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] :
    (moduleEmbedding J Λ).Faithful :=
  inferInstanceAs (sheafToPresheaf J (ModuleCat.{u} Λ) ⋙
    constantModulePresheaf J Λ).Faithful

private noncomputable def moduleExtension (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :=
  moduleEmbedding J Λ ⋙ PresheafOfModules.sheafification.{u} α

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

private noncomputable instance siteModuleSheafConstantRingEquivalenceInst5
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    (moduleExtension J Λ R α).Faithful :=
  Functor.Faithful.of_comp_iso (moduleEmbeddingUnitIso J Λ R α).symm

private noncomputable instance siteModuleSheafConstantRingEquivalenceInst6
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
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

private noncomputable instance siteModuleSheafConstantRingEquivalenceInst7
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
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

/-- Restriction of scalars along a locally bijective constant-ring unit is an equivalence,
compatible with constants and slice restriction.

Source: Stacks Project, Modules on Sites, Tag 093I; Cohomology on Sites, Tag 03FD.
(auxiliary; not a blueprint node).

Proof: retain the section modules and restrict their scalar actions along the ring unit.
The module-sheafification counit makes this functor inverse to extension of scalars.
The constant-presheaf unit gives the comparison on constants. Restricting a scalar action
and restricting to a slice commute sectionwise, including on morphisms. -/
theorem site_moduleSheaf_restriction_equivalence
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    let c := SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ ⋙
      PresheafOfModules.sheafification.{u} α
    ∃ G : SheafOfModules.{u} R ⥤ Sheaf J (ModuleCat.{u} Λ),
      G.IsEquivalence ∧ Nonempty (c ⋙ G ≅ constantSheaf J (ModuleCat.{u} Λ)) ∧
      ∀ U : C, ∃ GU : SheafOfModules.{u} (R.over U) ⥤
          Sheaf (J.over U) (ModuleCat.{u} Λ),
        GU.IsEquivalence ∧ Nonempty
          (SheafOfModules.overFunctor R U ⋙ GU ≅
            G ⋙ J.overPullback (ModuleCat.{u} Λ) U) := by
  refine ⟨moduleRestriction J Λ R α, inferInstance,
    ⟨moduleRestrictionConstantIso J Λ R α⟩, ?_⟩
  intro U
  let αU := Functor.whiskerLeft (Over.forget U).op α
  let : Presheaf.IsLocallyInjective (J.over U) αU :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α
  let : Presheaf.IsLocallySurjective (J.over U) αU :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α
  refine ⟨moduleRestriction (J.over U) Λ (R.over U) αU, inferInstance, ⟨?_⟩⟩
  exact NatIso.ofComponents (fun M ↦ Iso.refl _) (by cat_disch)

end CategoryTheory
