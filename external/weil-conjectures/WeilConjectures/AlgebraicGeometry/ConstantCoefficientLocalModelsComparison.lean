/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules

/-! # Comparison of the two constant coefficient module constructions

Source: Stacks Project, Cohomology on Sites, Tags 06YY and 094I.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

section Restriction

variable {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
  {R S : Sheaf T RingCat.{u}}

private noncomputable def restrictCancelIso (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    restrictScalars β ⋙ restrictScalars α ≅ 𝟭 (SheafOfModules.{u} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

attribute [local irreducible] restrictCancelIso

variable (T) in
noncomputable def restrictSheafificationComparison
    {R₀ S₀ : Cᵒᵖ ⥤ RingCat.{u}}
    (ηR : R₀ ⟶ R.obj) (ηS : S₀ ⟶ S.obj)
    [Presheaf.IsLocallyInjective T ηR] [Presheaf.IsLocallySurjective T ηR]
    [Presheaf.IsLocallyInjective T ηS] [Presheaf.IsLocallySurjective T ηS]
    (α₀ : R₀ ⟶ S₀) (α : R ⟶ S) (hsq : α₀ ≫ ηS = ηR ≫ α.hom)
    (P : PresheafOfModules.{u} S₀) :
    (PresheafOfModules.sheafification ηR).obj
      ((PresheafOfModules.restrictScalars α₀).obj P) ⟶
    (restrictScalars α).obj ((PresheafOfModules.sheafification ηS).obj P) := by
  let τ := (PresheafOfModules.sheafificationAdjunction ηS).unit.app P
  refine (PresheafOfModules.sheafificationHomEquiv ηR).symm ?_
  refine { app := ?_, naturality := ?_ }
  · intro U
    refine ModuleCat.ofHom
      (X := ((PresheafOfModules.restrictScalars α₀).obj P).obj U)
      (Y := ((PresheafOfModules.restrictScalars ηR).obj
        ((restrictScalars α).obj ((PresheafOfModules.sheafification ηS).obj P)).val).obj U)
      { toFun := τ.app U
        map_add' := map_add _
        map_smul' := ?_ }
    intro r x
    refine ((τ.app U).hom.map_smul (α₀.app U r) x).trans ?_
    change ηS.app U (α₀.app U r) •
        (show ((PresheafOfModules.sheafification ηS).obj P).val.obj U from τ.app U x) =
      α.hom.app U (ηR.app U r) •
        (show ((PresheafOfModules.sheafification ηS).obj P).val.obj U from τ.app U x)
    have hs := ConcreteCategory.congr_hom (congr_app hsq U) r
    change ηS.app U (α₀.app U r) = α.hom.app U (ηR.app U r) at hs
    rw [hs]
  · intro U V f
    ext x
    exact PresheafOfModules.naturality_apply τ f x

variable (T) in
theorem restrictSheafificationComparison_isIso
    {R₀ S₀ : Cᵒᵖ ⥤ RingCat.{u}}
    (ηR : R₀ ⟶ R.obj) (ηS : S₀ ⟶ S.obj)
    [Presheaf.IsLocallyInjective T ηR] [Presheaf.IsLocallySurjective T ηR]
    [Presheaf.IsLocallyInjective T ηS] [Presheaf.IsLocallySurjective T ηS]
    (α₀ : R₀ ⟶ S₀) (α : R ⟶ S) (hsq : α₀ ≫ ηS = ηR ≫ α.hom)
    (P : PresheafOfModules.{u} S₀) :
    IsIso (restrictSheafificationComparison T ηR ηS α₀ α hsq P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R)]
  have he : (toSheaf R).map
      (restrictSheafificationComparison T ηR ηS α₀ α hsq P) = 𝟙 _ := by
    unfold restrictSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      T AddCommGrpCat.{u}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rfl
  rw [he]
  infer_instance

attribute [local irreducible] restrictSheafificationComparison

end Restriction

private theorem preservesRingForgetSheafification
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C) :
    T.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u}) := by
  constructor
  intro P Q f hf
  change T.W (Functor.whiskerRight f (forget₂ CommRingCat.{u} RingCat.{u}))
  have hi : Presheaf.IsLocallyInjective T f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective T f := hf.isLocallySurjective
  apply (T.W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem T f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem T f x⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRingIso_fac
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    [T.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u})]
    (B : Type u) [CommRing B] :
    constantCoefficientUnit T B ≫ (((constantCommuteCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).app (CommRingCat.of B)).hom).hom =
      toSheafify T ((Functor.const Cᵒᵖ).obj (RingCat.of B)) := by
  simp only [Iso.app_hom]
  rw [constantCommuteCompose_hom_app_hom]
  unfold constantCoefficientUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality T
    (Functor.constComp Cᵒᵖ (CommRingCat.of B)
      (forget₂ CommRingCat.{u} RingCat.{u})).hom).symm.trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def constantModelsIso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    (e : constantCoefficientRing T B ≅ (constantSheaf T RingCat.{u}).obj (RingCat.of B))
    (hunit : constantCoefficientUnit T B ≫ e.hom.hom =
      toSheafify T ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
    (M : ModuleCat.{u} B) :
    (strictPerfectConstantSheaf T B).obj M ≅
      (restrictScalars e.inv).obj
        ((constantCoefficientModule T B).obj M) := by
  let η : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶
      ((constantSheaf T RingCat.{u}).obj (RingCat.of B)).obj :=
    toSheafify T ((Functor.const Cᵒᵖ).obj (RingCat.of B))
  have hsq : 𝟙 _ ≫ constantCoefficientUnit T B =
      η ≫ e.inv.hom := by
    dsimp only [η]
    rw [Category.id_comp, ← hunit, Category.assoc]
    change _ = _ ≫ (e.hom ≫ e.inv).hom
    rw [Iso.hom_inv_id]
    rfl
  let P := (strictPerfectConstantPresheaf (C := C) B).obj M
  have := restrictSheafificationComparison_isIso T η (constantCoefficientUnit T B)
    (𝟙 _) e.inv hsq P
  exact asIso (restrictSheafificationComparison T η (constantCoefficientUnit T B)
    (𝟙 _) e.inv hsq P)

attribute [local irreducible] constantModelsIso

set_option backward.isDefEq.respectTransparency false in
private theorem compare_of_iso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    (e : constantCoefficientRing T B ≅ (constantSheaf T RingCat.{u}).obj (RingCat.of B))
    (hunit : constantCoefficientUnit T B ≫ e.hom.hom =
      toSheafify T ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
    (F : SheafOfModules.{u} (constantCoefficientRing T B)) :
    IsLocallyConstantFiniteTypeModules T B F ↔
      IsFiniteTypeLocallyConstant T B ((restrictScalars e.inv).obj F) := by
  constructor
  · intro h V
    obtain ⟨S, hS, hs⟩ := h V
    refine ⟨S, hS, ?_⟩
    intro U f hf
    obtain ⟨M, hM, ⟨i⟩⟩ := hs U f hf
    let eU := (Functor.sheafPushforwardContinuous (Over.forget U) RingCat.{u}
      (T.over U) T).mapIso e
    refine ⟨M, hM, ⟨?_⟩⟩
    exact (restrictScalars eU.inv).mapIso i ≪≫
      ((overFunctor _ U).mapIso (constantModelsIso T B e hunit M)).symm
  · intro h V
    obtain ⟨S, hS, hs⟩ := h V
    refine ⟨S, hS, ?_⟩
    intro U f hf
    obtain ⟨M, hM, ⟨i⟩⟩ := hs U f hf
    let eU := (Functor.sheafPushforwardContinuous (Over.forget U) RingCat.{u}
      (T.over U) T).mapIso e
    let cancel := restrictCancelIso eU.hom eU.inv eU.hom_inv_id
    refine ⟨M, hM, ⟨?_⟩⟩
    exact (cancel.app (F.over U)).symm ≪≫ (restrictScalars eU.hom).mapIso
      (i ≪≫ ((overFunctor _ U).mapIso (constantModelsIso T B e hunit M))) ≪≫
        (cancel.app (((constantCoefficientModule T B).obj M).over U))

/-- The finite local constant-module descriptions formed by sheafifying in
commutative rings agree with those formed in rings. Source: Stacks Project,
Modules on Sites, Tag 093U; Cohomology on Sites, Tag 094I
(auxiliary; not a blueprint node).

Proof: forgetting commutativity commutes with sheafification. The resulting
constant-ring isomorphism intertwines the two sheafification units. The module
sheafification adjunction then identifies the two constant-module constructions
after transporting coefficients. This identification is an isomorphism because
its underlying additive-group sheaf map is the identity. Restriction of scalars
commutes with slices and is an equivalence for a ring-sheaf isomorphism, so transport
each local constant finite-module trivialization in either direction. -/
theorem exists_constantCoefficientRing_localModels_comparison
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B] :
    ∃ e : constantCoefficientRing T B ≅ (constantSheaf T RingCat.{u}).obj (RingCat.of B),
      (constantCoefficientUnit T B ≫ e.hom.hom =
        toSheafify T ((Functor.const Cᵒᵖ).obj (RingCat.of B))) ∧
      ∀ F : SheafOfModules.{u} (constantCoefficientRing T B),
        IsLocallyConstantFiniteTypeModules T B F ↔
          IsFiniteTypeLocallyConstant T B ((restrictScalars e.inv).obj F) := by
  have : T.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u}) :=
    preservesRingForgetSheafification T
  let e := (constantCommuteCompose T
    (forget₂ CommRingCat.{u} RingCat.{u})).app (CommRingCat.of B)
  have he : constantCoefficientUnit T B ≫ e.hom.hom =
      toSheafify T ((Functor.const Cᵒᵖ).obj (RingCat.of B)) := coefficientRingIso_fac T B
  exact ⟨e, he, fun F ↦ compare_of_iso T B e he F⟩

end SheafOfModules
