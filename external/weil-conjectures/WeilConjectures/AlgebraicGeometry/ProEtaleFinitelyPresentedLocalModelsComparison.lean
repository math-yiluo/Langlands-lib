/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-! # Finitely presented local constant models on the pro-etale site

Source: Stacks Project, Tags 09AJ and 093U.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace ProFiniteModels

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Finite constant models on covering sieves of a fixed-coefficient site.
Source: Stacks Project, Tag 093U
(auxiliary; not a blueprint node). -/
def fixedModels {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (F : Sheaf J (ModuleCat.{max u v} B)) : Prop :=
  ∀ V : C, ∃ T : Sieve V, T ∈ J V ∧
    ∀ (W : C) (a : W ⟶ V), T a →
      ∃ M : ModuleCat.{max u v} B, Module.Finite B M ∧
        Nonempty (F.over W ≅ (constantSheaf (J.over W) (ModuleCat.{max u v} B)).obj M)

private noncomputable def restriction {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (R : Sheaf J RingCat.{max u v})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj) :
    SheafOfModules.{max u v} R ⥤ Sheaf J (ModuleCat.{max u v} B) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars a).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{max u v} B :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
      (forget₂ (ModuleCat.{max u v} B) AddCommGrpCat.{max u v}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars a).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private noncomputable def restrictionFF {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (R : Sheaf J RingCat.{max u v})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallySurjective J a] : (restriction J B R a).FullyFaithful where
  preimage {M N} φ :=
    { val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective a N.isSheaf).symm
        { app := φ.hom.app
          naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.hom.naturality f) x } }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable def constantPresheaf {C : Type u} [Category.{v} C]
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B) :
    PresheafOfModules.{max u v} ((Functor.const Cᵒᵖ).obj (RingCat.of B)) where
  obj _ := M
  map _ := 𝟙 M

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private noncomputable def constantComparison {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (R : Sheaf J RingCat.{max u v})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    (M : ModuleCat.{max u v} B) :
    (constantSheaf J (ModuleCat.{max u v} B)).obj M ⟶
      (restriction J B R a).obj
        ((PresheafOfModules.sheafification a).obj (constantPresheaf B M)) := by
  let η := (PresheafOfModules.sheafificationAdjunction a).unit.app (constantPresheaf B M)
  exact ((sheafificationAdjunction J (ModuleCat.{max u v} B)).homEquiv _ _).symm
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem constantComparison_isIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (R : Sheaf J RingCat.{max u v})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    (M : ModuleCat.{max u v} B) : IsIso (constantComparison J B R a M) := by
  let N := (restriction J B R a).obj
    ((PresheafOfModules.sheafification a).obj (constantPresheaf B M))
  let η := (PresheafOfModules.sheafificationAdjunction a).unit.app (constantPresheaf B M)
  let η' : (Functor.const Cᵒᵖ).obj M ⟶ N.obj :=
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }
  have hηi : Presheaf.IsLocallyInjective J η' := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf B M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{max u v}))
    infer_instance
  have hηs : Presheaf.IsLocallySurjective J η' := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf B M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{max u v}))
    infer_instance
  have hf : toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
      (constantComparison J B R a M).hom = η' := by
    exact ((sheafificationAdjunction J (ModuleCat.{max u v} B)).homEquiv
      ((Functor.const Cᵒᵖ).obj M) N).apply_symm_apply η'
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective J (constantComparison J B R a M).hom
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J η' hf
  · change Presheaf.IsLocallySurjective J (constantComparison J B R a M).hom
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hf

/-- Finite local constant models are invariant under isomorphism.
Source: Stacks Project, Tag 093U
(auxiliary; not a blueprint node). -/
theorem fixedModels_of_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    {F G : Sheaf J (ModuleCat.{max u v} B)} (e : F ≅ G)
    (h : fixedModels J B F) : fixedModels J B G := by
  intro V
  obtain ⟨T, hT, ht⟩ := h V
  refine ⟨T, hT, fun W f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := ht W f hf
  exact ⟨M, hM, ⟨(J.overPullback _ W).mapIso e.symm ≪≫ i⟩⟩

private theorem fixedModels_constantRing {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    (F : ringedSiteModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) :
    fixedModels J B ((constantRingModuleRestriction J B).obj F) ↔
      SheafOfModules.IsFiniteTypeLocallyConstant J B F := by
  let R := (constantSheaf J RingCat.{u}).obj (RingCat.of B)
  let a := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))
  have hi (W : C) (M : ModuleCat.{u} B) :
      Nonempty (F.over W ≅ ((SheafOfModules.strictPerfectConstantSheaf J B).obj M).over W) ↔
        Nonempty (((constantRingModuleRestriction J B).obj F).over W ≅
          (constantSheaf (J.over W) (ModuleCat.{u} B)).obj M) := by
    let aW := Functor.whiskerLeft (Over.forget W).op a
    have : Presheaf.IsLocallySurjective (J.over W) aW :=
      Presheaf.isLocallySurjective_whisker (J.over W) J (Over.forget W) a
    let E := restriction (J.over W) B (R.over W) aW
    have := constantComparison_isIso J B R a M
    let c : (constantSheaf (J.over W) (ModuleCat.{u} B)).obj M ≅
        E.obj (((SheafOfModules.strictPerfectConstantSheaf J B).obj M).over W) :=
      ((J.overPullbackConstantSheafIso (ModuleCat.{u} B) W).app M).symm ≪≫
        (J.overPullback _ W).mapIso (asIso (constantComparison J B R a M))
    constructor
    · rintro ⟨e⟩
      exact ⟨E.mapIso e ≪≫ c.symm⟩
    · rintro ⟨e⟩
      exact ⟨(restrictionFF (J.over W) B (R.over W) aW).preimageIso (e ≪≫ c)⟩
  constructor
  all_goals
    intro h V
    obtain ⟨T, hT, ht⟩ := h V
    refine ⟨T, hT, fun W f hf ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := ht W f hf
    first
    | exact ⟨M, hM, (hi W M).mpr he⟩
    | exact ⟨M, hM, (hi W M).mp he⟩

theorem asSmallDownEquivalence {C : Type u} [Category.{v} C] :
    (AsSmall.down : AsSmall.{w} C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{w} C).isEquivalence_inverse

theorem asSmallUpEquivalence {C : Type u} [Category.{v} C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{w} C).isEquivalence_functor

attribute [local instance] asSmallDownEquivalence asSmallUpEquivalence

theorem asSmallDense {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    (show C ≌ AsSmall.{max u v} C from AsSmall.equiv).inverse.IsDenseSubsite
      (AsSmall.down.inducedTopology J) J := by
  change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology J) J
  infer_instance

attribute [local instance] asSmallDense

theorem asSmallUpDense {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    (AsSmall.up : C ⥤ AsSmall.{max u v} C).IsDenseSubsite J
      (AsSmall.down.inducedTopology J) :=
  inferInstanceAs ((AsSmall.equiv : C ≌ AsSmall.{max u v} C).functor.IsDenseSubsite J
    (AsSmall.down.inducedTopology J))

attribute [local instance] asSmallDownEquivalence asSmallUpEquivalence
  asSmallDense asSmallUpDense

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem fixedModels_asSmall {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (B : Type (max u v)) [CommRing B]
    (F : Sheaf J (ModuleCat.{max u v} B)) :
    fixedModels J B F ↔
      fixedModels ((show AsSmall.{max u v} C ⥤ C from AsSmall.down).inducedTopology J) B
        (((show C ≌ AsSmall.{max u v} C from AsSmall.equiv).sheafCongr J
          (AsSmall.down.inducedTopology J) (ModuleCat.{max u v} B)).functor.obj F) := by
  let K := (show AsSmall.{max u v} C ⥤ C from AsSmall.down).inducedTopology J
  let H := ((show C ≌ AsSmall.{max u v} C from AsSmall.equiv).sheafCongr J K
    (ModuleCat.{max u v} B)).functor.obj F
  have hs (W : AsSmall.{max u v} C) :
      (Over.post (X := W) AsSmall.down).IsDenseSubsite
        (K.over W) (J.over (AsSmall.down.obj W)) := by
    refine { functorPushforward_mem_iff := ?_ }
    intro Z S
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff]
    rw [Sieve.overEquiv_functorPushforward_post]
    exact AsSmall.down.functorPushforward_mem_iff K J
  have hc (W : AsSmall.{max u v} C) (M : ModuleCat.{max u v} B) :
      Nonempty (F.over (AsSmall.down.obj W) ≅
        (constantSheaf (J.over (AsSmall.down.obj W)) _).obj M) ↔
        Nonempty (H.over W ≅ (constantSheaf (K.over W) _).obj M) := by
    let e := (Over.post (X := W) AsSmall.down).asEquivalence.symm
    have : e.inverse.IsDenseSubsite (K.over W) (J.over (AsSmall.down.obj W)) := by
      change (Over.post (X := W) AsSmall.down).IsDenseSubsite _ _
      exact hs W
    let E := e.sheafCongr (J.over (AsSmall.down.obj W)) (K.over W) (ModuleCat.{max u v} B)
    let i : E.functor.obj (F.over (AsSmall.down.obj W)) ≅ H.over W := Iso.refl _
    let c := (e.constantSheafSheafCongrIso (J.over (AsSmall.down.obj W)) (K.over W)
      (ModuleCat.{max u v} B) Over.mkIdTerminal).app M
    constructor
    · rintro ⟨q⟩
      exact ⟨i.symm ≪≫ E.functor.mapIso q ≪≫ c⟩
    · rintro ⟨q⟩
      exact ⟨E.unitIso.app _ ≪≫ E.inverse.mapIso (i ≪≫ q ≪≫ c.symm) ≪≫
        (E.unitIso.app _).symm⟩
  constructor
  · intro h V
    obtain ⟨T, hT, ht⟩ := h (AsSmall.down.obj V)
    refine ⟨T.functorPullback AsSmall.down, ?_, fun W f hf ↦ ?_⟩
    · exact AsSmall.down.cover_lift K J hT
    · obtain ⟨M, hM, he⟩ := ht (AsSmall.down.obj W) f.down hf
      exact ⟨M, hM, (hc W M).mp he⟩
  · intro h V
    obtain ⟨T, hT, ht⟩ := h (AsSmall.up.obj V)
    refine ⟨T.functorPullback AsSmall.up, ?_, fun W f hf ↦ ?_⟩
    · exact AsSmall.up.cover_lift J K hT
    · obtain ⟨M, hM, he⟩ := ht (AsSmall.up.obj W) (AsSmall.up.map f) hf
      exact ⟨M, hM, (hc (AsSmall.up.obj W) M).mpr he⟩

end ProFiniteModels

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense

end AlgebraicGeometry.Scheme
