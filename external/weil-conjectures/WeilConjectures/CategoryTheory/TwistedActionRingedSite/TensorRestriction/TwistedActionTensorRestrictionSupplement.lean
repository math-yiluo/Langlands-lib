/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.CategoryTheory.TwistedActionTensorRestriction

/-! # Explicit tensor comparisons for restriction of module sheaves

The comparison is constructed by transposing the restricted sheafification unit.
For a continuous cocontinuous functor and an isomorphism of coefficient rings,
it is invertible and carries sheafified pure tensors to pure tensors.
Source: Stacks 03CY and 03EK; the module-sheafification adjunction.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite.TensorRestriction

section SheafificationComparison

universe c v r c₂ v₂

@[irreducible] noncomputable def restrictionSheafificationMap
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
        (SheafOfModules.pushforward.{r} φ).obj
          ((PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 _)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P))

theorem restrictionSheafificationMap_unit
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    toSheafify K (F.op ⋙ P.presheaf) ≫
        (PresheafOfModules.toPresheaf.{r} _).map (restrictionSheafificationMap φ P).val =
      Functor.whiskerLeft F.op (toSheafify L P.presheaf) := by
  have h := (PresheafOfModules.sheafificationHomEquiv.{r} (R := S) (𝟙 _)
    (P := (PresheafOfModules.pushforward φ.hom).obj P)
    (F := (SheafOfModules.pushforward.{r} φ).obj
      ((PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P))).apply_symm_apply
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P))
  unfold restrictionSheafificationMap
  exact congrArg ((PresheafOfModules.toPresheaf.{r} S.obj).map) h

theorem restrictionSheafificationMap_unit_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) (U : Dᵒᵖ)
    (z : ((PresheafOfModules.pushforward φ.hom).obj P).obj U) :
    (restrictionSheafificationMap φ P).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app
        ((PresheafOfModules.pushforward φ.hom).obj P)).app U z) =
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P).app
        (F.op.obj U) z := by
  exact congrArg (fun k ↦ k.app U z) (restrictionSheafificationMap_unit φ P)

theorem pushforward_four_comp_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    {A B C : SheafOfModules.{r} S} {P Q : SheafOfModules.{r} R}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ (SheafOfModules.pushforward φ).obj P)
    (d : P ⟶ Q) (U : Dᵒᵖ) (z : A.val.obj U) :
    (a ≫ b ≫ c ≫ (SheafOfModules.pushforward φ).map d).val.app U z =
      d.val.app (F.op.obj U) (c.val.app U (b.val.app U (a.val.app U z))) := rfl

theorem sheaf_iso_inv_hom_apply
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{r}} {M N : SheafOfModules.{r} S}
    (T : M ≅ N) (U : Dᵒᵖ) (z : N.val.obj U) :
    T.hom.val.app U (T.inv.val.app U z) = z := by
  exact congrArg (fun k ↦ k.val.app U z) T.inv_hom_id

theorem sheafification_unit_naturality_apply
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf K RingCat.{r}) {P Q : PresheafOfModules.{r} S.obj} (f : P ⟶ Q)
    (U : Dᵒᵖ) (z : P.obj U) :
    ((PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).map f).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app P).app
        U z) =
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app Q).app
        U (f.app U z) := by
  exact congrArg (fun k ↦ k.app U z)
    ((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.naturality f).symm

theorem tensorComparison_unit_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) (Q : PresheafOfModules.{r} S.obj)
    (t : Q ⟶ (PresheafOfModules.pushforward φ.hom).obj P)
    {A : SheafOfModules.{r} S} {B : SheafOfModules.{r} R}
    (T : A ≅ (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).obj Q)
    (V : B ≅ (PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P)
    (U : Dᵒᵖ) (z : Q.obj U) :
    (T.hom ≫ (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).map t ≫
        restrictionSheafificationMap φ P ≫ (SheafOfModules.pushforward φ).map V.inv).val.app U
      (T.inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app Q).app
          U z)) =
      V.inv.val.app (F.op.obj U)
        (((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P).app
          (F.op.obj U) (t.app U z)) := by
  rw [pushforward_four_comp_apply, sheaf_iso_inv_hom_apply,
    sheafification_unit_naturality_apply, restrictionSheafificationMap_unit_apply]

theorem restrictionSheafificationMap_isIso
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L] [F.IsCocontinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    IsIso (restrictionSheafificationMap φ P) := by
  let a := toSheafify K (F.op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf.{r} _).map (restrictionSheafificationMap φ P).val
  have hi : Presheaf.IsLocallyInjective K
      (Functor.whiskerLeft F.op (toSheafify L P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker K L F _
  have hs : Presheaf.IsLocallySurjective K
      (Functor.whiskerLeft F.op (toSheafify L P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker K L F _
  have hi' : Presheaf.IsLocallyInjective K b := by
    rw [← Presheaf.comp_isLocallyInjective_iff K a b]
    rw [restrictionSheafificationMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective K b := by
    rw [← Presheaf.comp_isLocallySurjective_iff K a b]
    rw [restrictionSheafificationMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{r} S)]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · exact (Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hi'
  · exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hs'

theorem restrictScalars_mu_bijective (R S : Type r) [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat.{r} S) :
    Function.Bijective (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm
  let em : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((ModuleCat.restrictScalars e.toRingHom).obj M) M :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change (e.toRingHom r) • x = (e.toRingHom r) • x
        rfl }
  let en : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((ModuleCat.restrictScalars e.toRingHom).obj N) N :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change (e.toRingHom r) • x = (e.toRingHom r) • x
        rfl }
  have hh : (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N :
      _ → _) = TensorProduct.congr em en := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact ModuleCat.restrictScalars_μ_tmul e.toRingHom M N x y
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hh]
  exact (TensorProduct.congr em en).bijective

theorem restrictScalars_mu_isIso (R S : Type r) [CommRing R] [CommRing S]
    (f : R →+* S) (M N : ModuleCat.{r} S)
    (hf : Function.Bijective f) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars f) M N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact restrictScalars_mu_bijective R S (RingEquiv.ofBijective f hf) M N

end SheafificationComparison

theorem iso_section_injective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (T : M ≅ N) (X : Cᵒᵖ) :
    Function.Injective (T.hom.val.app X) :=
  Function.LeftInverse.injective (g := T.inv.val.app X)
    (fun z ↦ congrArg (fun k ↦ k.val.app X z) T.hom_inv_id)

theorem tensorIso_natural {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {M M' N N' : Modules R} (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap f g ≫ (SheafOfModules.tensorObjIsoSheafification M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ring R).obj)).map (f.val ⊗ₘ g.val) := by
  change (f ⊗ₘ g) ≫ _ = _
  rw [tensorHom_def, Category.assoc]
  erw [SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom (R := R) M' g]
  rw [← Category.assoc]
  erw [SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom (R := R) f N]
  rw [Category.assoc, ← Functor.map_comp, ← tensorHom_def]

theorem pure_ext {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    (M N H : Modules R) {f g : tensorObj M N ⟶ H}
    (h : ∀ X x y, f.val.app X (pureTensor M N X x y) =
      g.val.app X (pureTensor M N X x y)) : f = g := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ring R).obj)).homEquiv _ H).injective
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h X x y

theorem pure_map {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {M M' N N' : Modules R} (f : M ⟶ M') (g : N ⟶ N') (X : Cᵒᵖ)
    (x : M.val.obj X) (y : N.val.obj X) :
    (tensorMap f g).val.app X (pureTensor M N X x y) =
      pureTensor M' N' X (f.val.app X x) (g.val.app X y) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ring R).obj)
  have h : (SheafOfModules.tensorObjIsoSheafification M N).inv ≫ tensorMap f g =
      (PresheafOfModules.sheafification (𝟙 (ring R).obj)).map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun k ↦ k.app X (x ⊗ₜ[R.obj.obj X] y))
    (adj.unit.naturality (f.val ⊗ₘ g.val))
  have he := congrArg (fun k ↦ k.val.app X
    ((adj.unit.app (M.val ⊗ N.val)).app X (x ⊗ₜ[R.obj.obj X] y))) h
  exact he.trans
    (congrArg ((SheafOfModules.tensorObjIsoSheafification M' N').inv.val.app X) hh.symm)

theorem pure_restrict {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    (M N : Modules R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : M.val.obj X) (y : N.val.obj X) :
    (tensorObj M N).val.map f (pureTensor M N X x y) =
      pureTensor M N Y (M.val.map f x) (N.val.map f y) := by
  unfold pureTensor
  rw [← PresheafOfModules.naturality_apply]
  congr 1
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring R).obj)).unit.app
      (M.val ⊗ N.val)) f (x ⊗ₜ[R.obj.obj X] y)).symm

section RestrictionTensor

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
    (c : (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R ≅ S)

noncomputable abbrev coefficientMap :
    ring S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ring R) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv

noncomputable abbrev restrictionFunctor : Modules R ⥤ Modules S :=
  SheafOfModules.pushforward (F := F) (J := J) (K := K)
    (R := ring R) (S := ring S) (coefficientMap F R S c)

noncomputable def tensorPushMap (M N : Modules R) :
    tensorObj ((restrictionFunctor F R S c).obj M) ((restrictionFunctor F R S c).obj N) ⟶
      (restrictionFunctor F R S c).obj (tensorObj M N) :=
  (SheafOfModules.tensorObjIsoSheafification
    ((restrictionFunctor F R S c).obj M) ((restrictionFunctor F R S c).obj N)).hom ≫
    (PresheafOfModules.sheafification (𝟙 (ring S).obj)).map
      (Functor.LaxMonoidal.μ (PresheafOfModules.pushforward (F := F)
        (R := R.obj ⋙ forget₂ CommRingCat RingCat)
        (S := S.obj ⋙ forget₂ CommRingCat RingCat)
        (Functor.whiskerRight c.inv.hom (forget₂ CommRingCat RingCat))) M.val N.val) ≫
    restrictionSheafificationMap (coefficientMap F R S c) (M.val ⊗ N.val) ≫
    (restrictionFunctor F R S c).map (SheafOfModules.tensorObjIsoSheafification M N).inv

private theorem presheaf_tensorator_pure (M N : Modules R) (X : Cᵒᵖ)
    (x : M.val.obj (F.op.obj X)) (y : N.val.obj (F.op.obj X)) :
    (Functor.LaxMonoidal.μ (PresheafOfModules.pushforward (F := F)
      (R := R.obj ⋙ forget₂ CommRingCat RingCat)
      (S := S.obj ⋙ forget₂ CommRingCat RingCat)
      (Functor.whiskerRight c.inv.hom (forget₂ CommRingCat RingCat))) M.val N.val).app X
        (x ⊗ₜ[S.obj.obj X] y) = x ⊗ₜ[R.obj.obj (F.op.obj X)] y := by
  exact ModuleCat.restrictScalars_μ_tmul
    (c.inv.hom.app X).hom (M.val.obj (F.op.obj X)) (N.val.obj (F.op.obj X)) x y

theorem tensorPushMap_pure (M N : Modules R) (X : Cᵒᵖ)
    (x : M.val.obj (F.op.obj X)) (y : N.val.obj (F.op.obj X)) :
    (tensorPushMap F R S c M N).val.app X
      (pureTensor _ _ X x y) = pureTensor M N (F.op.obj X) x y := by
  have h := tensorComparison_unit_apply (coefficientMap F R S c) (M.val ⊗ N.val)
    (((restrictionFunctor F R S c).obj M).val ⊗
      ((restrictionFunctor F R S c).obj N).val)
    (Functor.LaxMonoidal.μ (PresheafOfModules.pushforward (F := F)
      (R := R.obj ⋙ forget₂ CommRingCat RingCat)
      (S := S.obj ⋙ forget₂ CommRingCat RingCat)
      (Functor.whiskerRight c.inv.hom (forget₂ CommRingCat RingCat))) M.val N.val)
    (SheafOfModules.tensorObjIsoSheafification
      ((restrictionFunctor F R S c).obj M) ((restrictionFunctor F R S c).obj N))
    (SheafOfModules.tensorObjIsoSheafification M N) X
    (x ⊗ₜ[S.obj.obj X] y)
  exact h.trans (congrArg
    (fun z : (M.val ⊗ N.val).obj (F.op.obj X) ↦
      (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app (F.op.obj X)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ring R).obj)).unit.app
          (M.val ⊗ N.val)).app (F.op.obj X) z))
    (presheaf_tensorator_pure F R S c M N X x y))

/-- The explicit tensorator is invertible when restriction commutes with sheafification.
Source: Stacks 03CY and 03EK; the sectionwise tensor and sheafification adjunction.
(blueprint: lem-sf-cocontinuous-ringed-tensor-restriction).

Proof: the coefficient isomorphism makes the sectionwise scalar-restriction tensorator
invertible, by tensoring the two semilinear identity equivalences. Sheafification preserves
that isomorphism. Compose with the assumed sheafification comparison and the canonical
sheaf-tensor isomorphisms. The preceding unit equation identifies the result on pure tensors.
For a continuous cocontinuous functor, the assumption is proved above: restriction preserves
the local bijectivity of the sheafification unit, so its transpose is an isomorphism.
-/
theorem tensorPushMap_isIso
    (h : ∀ Q : PresheafOfModules.{u} (ring R).obj,
      IsIso (restrictionSheafificationMap (coefficientMap F R S c) Q))
    (M N : Modules R) : IsIso (tensorPushMap F R S c M N) := by
  let G := PresheafOfModules.pushforward (F := F)
    (R := R.obj ⋙ forget₂ CommRingCat RingCat)
    (S := S.obj ⋙ forget₂ CommRingCat RingCat)
    (Functor.whiskerRight c.inv.hom (forget₂ CommRingCat RingCat))
  let m := Functor.LaxMonoidal.μ G M.val N.val
  have hm (X : Cᵒᵖ) : IsIso (m.app X) := by
    dsimp only [m, G]
    erw [PresheafOfModules.pushforward_μ_app]
    apply restrictScalars_mu_isIso
    exact ConcreteCategory.bijective_of_isIso
      (((sheafCompose J (forget₂ CommRingCat RingCat)).mapIso c.symm).hom.hom.app X)
  let e := PresheafOfModules.isoMk
    (fun X ↦ @asIso _ _ _ _ (m.app X) (hm X)) (fun {_ _} f ↦ m.naturality f)
  have he : e.hom = m := by
    apply PresheafOfModules.hom_ext
    intro X
    rfl
  have : IsIso m := by
    rw [← he]
    infer_instance
  have := h (M.val ⊗ N.val)
  unfold tensorPushMap
  infer_instance

theorem tensorPushMap_natural {M M' N N' : Modules R}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap ((restrictionFunctor F R S c).map f) ((restrictionFunctor F R S c).map g) ≫
        tensorPushMap F R S c M' N' =
      tensorPushMap F R S c M N ≫ (restrictionFunctor F R S c).map (tensorMap f g) := by
  apply pure_ext
  intro X x y
  change (tensorPushMap F R S c M' N').val.app X
      ((tensorMap _ _).val.app X (pureTensor _ _ X x y)) =
    (tensorMap f g).val.app (F.op.obj X)
      ((tensorPushMap F R S c M N).val.app X (pureTensor _ _ X x y))
  rw [pure_map, tensorPushMap_pure, tensorPushMap_pure, pure_map]
  rfl

noncomputable def restrictionUnitIso :
    (restrictionFunctor F R S c).obj (𝟙_ (Modules R)) ≅ 𝟙_ (Modules S) :=
  (SheafOfModules.fullyFaithfulForget (ring S)).preimageIso
    (PresheafOfModules.isoMk (fun X ↦ (show
      ((restrictionFunctor F R S c).obj (𝟙_ (Modules R))).val.obj X ≃ₗ[S.obj.obj X]
        (𝟙_ (Modules S)).val.obj X from
      { toFun := c.hom.hom.app X
        invFun := c.inv.hom.app X
        left_inv := fun x ↦ congrArg (fun k ↦ k.hom.app X x) c.hom_inv_id
        right_inv := fun x ↦ congrArg (fun k ↦ k.hom.app X x) c.inv_hom_id
        map_add' := map_add _
        map_smul' := fun r x ↦ by
          have hm := (c.hom.hom.app X).hom.map_mul (c.inv.hom.app X r)
            (show R.obj.obj (F.op.obj X) from x)
          have hi : (c.hom.hom.app X) ((c.inv.hom.app X) r) = r :=
            congrArg (fun k ↦ k.hom.app X r) c.inv_hom_id
          rw [hi] at hm
          exact hm }).toModuleIso)
      (fun {X Y} f ↦ by
        ext x
        exact congrArg (fun k ↦ k x) (c.hom.hom.naturality f)))

end RestrictionTensor

attribute [irreducible] tensorPushMap

end CategoryTheory.TwistedActionRingedSite.TensorRestriction
