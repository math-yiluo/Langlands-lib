/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients

/-! # The ordinary balanced coefficient comparison

Source: Stacks Project, Modules on Sites, Tags 03EK and 05V4.
-/

@[expose] public section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
open SheafOfModules.SuccessiveDerivedQuotient
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [∀ A : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules A)]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

section Construction
variable (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
  (N : Normalization p) {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)

private noncomputable def ordinaryReductionMap {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) : restriction φ ⋙ (p (φ ≫ ψ)).ordinary ⟶ (p ψ).ordinary where
  app M := (N.ordinary φ ψ).inv.app ((restriction φ).obj M) ≫
    (p ψ).ordinary.map ((N.ordinaryAdjunction φ).counit.app M)
  naturality {M M'} f := by
    dsimp
    rw [(N.ordinary φ ψ).inv.naturality_assoc]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun k ↦ (N.ordinary φ ψ).inv.app ((restriction φ).obj M) ≫
      (p ψ).ordinary.map k) ((N.ordinaryAdjunction φ).counit.naturality f)

omit [EssentiallySmall.{r} C] in
private theorem sectionTensor_smul {A S : Sheaf J CommRingCat.{r}} (a : A ⟶ S)
    (M : Modules A) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionTensor (p a) M U s x = s • sectionTensor (p a) M U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (changeOfRingsPresheaf a M)
  change (eqToHom ((p a).obj_eq M).symm).val.app U
      (η.app U (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)) =
    s • (eqToHom ((p a).obj_eq M).symm).val.app U
      (η.app U ((1 : S.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x))
  rw [← ((eqToHom ((p a).obj_eq M).symm).val.app U).hom.map_smul]
  rw [← (η.app U).hom.map_smul]
  congr 2
  change s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x =
    (s * 1) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x
  rw [mul_one]

include N in
private theorem sectionTensor_map {A S : Sheaf J CommRingCat.{r}} (a : A ⟶ S)
    {M M' : Modules A} (f : M ⟶ M') (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : M.val.obj U) :
    ((p a).ordinary.map f).val.app U (sectionTensor (p a) M U s x) =
      sectionTensor (p a) M' U s (f.val.app U x) := by
  have h := congrArg (fun k ↦ k.val.app U x) ((N.ordinaryAdjunction a).unit.naturality f).symm
  change ((p a).ordinary.map f).val.app U
    (((N.ordinaryAdjunction a).unit.app M).val.app U x) =
      ((N.ordinaryAdjunction a).unit.app M').val.app U (f.val.app U x) at h
  simp only [N.ordinary_unit] at h
  calc
    _ = ((p a).ordinary.map f).val.app U (s • sectionTensor (p a) M U 1 x) :=
      congrArg (fun z ↦ ((p a).ordinary.map f).val.app U z) (sectionTensor_smul p a M U s x)
    _ = s • ((p a).ordinary.map f).val.app U (sectionTensor (p a) M U 1 x) :=
      (((p a).ordinary.map f).val.app U).hom.map_smul _ _
    _ = s • sectionTensor (p a) M' U 1 (f.val.app U x) := congrArg (s • ·) h
    _ = _ := (sectionTensor_smul p a M' U s (f.val.app U x)).symm

private theorem ordinaryReductionMap_pure {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((ordinaryReductionMap p N φ ψ).app M).val.app U
      (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
        sectionTensor (p ψ) M U s x := by
  change ((p ψ).ordinary.map ((N.ordinaryAdjunction φ).counit.app M)).val.app U
    (((N.ordinary φ ψ).inv.app ((restriction φ).obj M)).val.app U
      (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x)) = _
  erw [N.ordinary_inv, sectionTensor_map p N]
  have h := congrArg (fun k ↦ k.val.app U x)
    ((N.ordinaryAdjunction φ).right_triangle_components M)
  change ((N.ordinaryAdjunction φ).counit.app M).val.app U
    (((N.ordinaryAdjunction φ).unit.app ((restriction φ).obj M)).val.app U x) = x at h
  rw [N.ordinary_unit] at h
  rw [h]
  rfl

private noncomputable def tensorPure (A : Sheaf J CommRingCat.{r})
    (M N : Modules A) (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((monoidalCategory A).tensorObj M N).val.obj V :=
  (tensorObjIsoSheafification M N).inv.val.app V
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y))

set_option linter.unusedSectionVars false in
private theorem tensorPure_map (A : Sheaf J CommRingCat.{r})
    {M M' N N' : Modules A} (f : M ⟶ M') (g : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((monoidalCategory A).tensorHom f g).val.app V (tensorPure A M N V x y) =
      tensorPure A M' N' V (f.val.app V x) (g.val.app V y) := by
  let := monoidalCategory A
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  have ht : (f ⊗ₘ g) ≫ (tensorObjIsoSheafification M' N').hom =
      (tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) := by
    let sh := PresheafOfModules.sheafification (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
    let ε := asIso adj.counit
    have hf : f ≫ (ε.app M').inv = (ε.app M).inv ≫ sh.map f.val :=
      ε.inv.naturality f
    have hg : g ≫ (ε.app N').inv = (ε.app N).inv ≫ sh.map g.val :=
      ε.inv.naturality g
    change (f ⊗ₘ g) ≫ ((ε.app M').inv ⊗ₘ (ε.app N').inv) ≫
        Functor.LaxMonoidal.μ sh M'.val N'.val =
      ((ε.app M).inv ⊗ₘ (ε.app N).inv) ≫
        Functor.LaxMonoidal.μ sh M.val N.val ≫ sh.map (f.val ⊗ₘ g.val)
    rw [← Functor.LaxMonoidal.μ_natural]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, hf, hg]
  have hi : (tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← ht, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun h ↦ h.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y))) hi
  have hη := congrArg (fun h ↦ h.app V (x ⊗ₜ[A.obj.obj V] y))
    (adj.unit.naturality (f.val ⊗ₘ g.val))
  exact hh.trans (congrArg ((tensorObjIsoSheafification M' N').inv.val.app V) hη.symm)

set_option linter.unusedSectionVars false in
private theorem tensorPure_hom_ext (A : Sheaf J CommRingCat.{r})
    (M N H : Modules A)
    {f g : (monoidalCategory A).tensorObj M N ⟶ H}
    (h : ∀ V x y, f.val.app V (tensorPure A M N V x y) =
      g.val.app V (tensorPure A M N V x y)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

set_option linter.unusedSectionVars false in
private theorem restrictSheafify_hom_section
    {A D : Sheaf J RingCat.{r}} (a : A ⟶ D)
    (P : PresheafOfModules.{r} D.obj) (U : Cᵒᵖ)
    (x : ((PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars a.hom).obj P)).val.obj U) :
    (cancellationRestrictSheafifyIso a P).hom.val.app U x = x := by
  exact congrArg (fun k ↦ k.hom.app U x) (cancellationRestrictSheafifyHom_toSheaf a P)

private theorem restrictSheafify_inv_section
    {A D : Sheaf J RingCat.{r}} (a : A ⟶ D)
    (P : PresheafOfModules.{r} D.obj) (U : Cᵒᵖ)
    (x : ((restrictScalars a).obj
      ((PresheafOfModules.sheafification (𝟙 D.obj)).obj P)).val.obj U) :
    (cancellationRestrictSheafifyIso a P).inv.val.app U x = x := by
  have h := congrArg (fun k ↦ k.val.app U x)
    (cancellationRestrictSheafifyIso a P).inv_hom_id
  change (cancellationRestrictSheafifyIso a P).hom.val.app U
    ((cancellationRestrictSheafifyIso a P).inv.val.app U x) = x at h
  rwa [restrictSheafify_hom_section] at h

private noncomputable def restrictionExtensionTensorIso
    {A D : Sheaf J CommRingCat.{r}} (a : A ⟶ D) (M : Modules A) :
    (restriction a).obj ((p a).ordinary.obj M) ≅
      (monoidalCategory A).tensorObj M
        ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J D))) :=
  (restriction a).mapIso (eqToIso ((p a).obj_eq M)) ≪≫
    (cancellationRestrictSheafifyIso
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)
      (changeOfRingsPresheaf a M)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙
      (derivedChangeRingIndependentCoefficients J A).obj)).mapIso
      (presheafTensorIso a M ≪≫ β_ _ _) ≪≫
    (tensorObjIsoSheafification M
      ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J D)))).symm

private theorem restrictionExtensionTensorIso_pure
    {A D : Sheaf J CommRingCat.{r}} (a : A ⟶ D) (M : Modules A)
    (U : Cᵒᵖ) (s : D.obj.obj U) (x : M.val.obj U) :
    (restrictionExtensionTensorIso p a M).hom.val.app U
      (sectionTensor (p a) M U s x) =
        tensorPure A M
          ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J D)))
            U x s := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J A).obj)
  let q := (presheafTensorIso a M ≪≫ β_ _ _).hom
  have hn := congrArg (fun k ↦ k.app U
    (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)) (adj.unit.naturality q)
  dsimp only [restrictionExtensionTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, sectionTensor]
  have he := congrArg (fun k ↦ k.val.app U (pure a M U s x))
    (eqToIso ((p a).obj_eq M)).inv_hom_id
  change (eqToHom ((p a).obj_eq M)).val.app U
    ((eqToHom ((p a).obj_eq M).symm).val.app U (pure a M U s x)) =
      pure a M U s x at he
  change (tensorObjIsoSheafification M _).inv.val.app U
    (((PresheafOfModules.sheafification (𝟙 _)).map q).val.app U
      ((cancellationRestrictSheafifyIso _ _).inv.val.app U
        ((eqToHom ((p a).obj_eq M)).val.app U
          ((eqToHom ((p a).obj_eq M).symm).val.app U (pure a M U s x))))) = _
  rw [he, restrictSheafify_inv_section]
  exact congrArg ((tensorObjIsoSheafification M _).inv.val.app U) hn.symm

private theorem cancellationSheafIso_inv_pure
    {A D : Sheaf J CommRingCat.{r}} (a : A ⟶ D)
    (M : Modules D) (K : Modules A) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : K.val.obj U) :
    (cancellationSheafIso a M K).inv.val.app U
      (tensorPure A ((restriction a).obj M) K U x y) =
        tensorPure D M (changeOfRings a K) U x (pure a K U 1 y) := by
  let adjA := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J A).obj)
  let adjD := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J D).obj)
  let q := (cancellationPresheafIso a M K).inv
  have hq := congrArg (fun k ↦ k.app U (x ⊗ₜ[A.obj.obj U] y))
    (adjA.unit.naturality q)
  have ht := congrArg (fun k ↦ k.val.app U
    ((adjA.unit.app (((restriction a).obj M).val ⊗ K.val)).app U
      (x ⊗ₜ[A.obj.obj U] y)))
    (tensorObjIsoSheafification ((restriction a).obj M) K).inv_hom_id
  change (tensorObjIsoSheafification ((restriction a).obj M) K).hom.val.app U
    (tensorPure A ((restriction a).obj M) K U x y) =
      (adjA.unit.app (((restriction a).obj M).val ⊗ K.val)).app U
        (x ⊗ₜ[A.obj.obj U] y) at ht
  dsimp only [cancellationSheafIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Functor.mapIso_hom]
  change (cancellationTensorSheafifyIso a M K).hom.val.app U
    ((cancellationRestrictSheafifyIso _ _).hom.val.app U
      (((PresheafOfModules.sheafification (𝟙 _)).map q).val.app U
        ((tensorObjIsoSheafification ((restriction a).obj M) K).hom.val.app U
          (tensorPure A ((restriction a).obj M) K U x y)))) = _
  rw [ht]
  erw [← hq, restrictSheafify_hom_section]
  let η := adjD.unit.app (changeOfRingsPresheaf a K)
  have hη := congrArg (fun k ↦ k.app U
    (x ⊗ₜ[D.obj.obj U] ((1 : D.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] y)))
      (adjD.unit.naturality (M.val ◁ η))
  change (tensorObjIsoSheafification M (changeOfRings a K)).inv.val.app U
    (((PresheafOfModules.sheafification (𝟙 _)).map (M.val ◁ η)).val.app U
      ((adjD.unit.app (M.val ⊗ changeOfRingsPresheaf a K)).app U
        (x ⊗ₜ[D.obj.obj U]
          ((1 : D.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] y)))) = _
  exact congrArg ((tensorObjIsoSheafification M _).inv.val.app U) hη.symm

private theorem restrictionComp_inv_section {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S) (M : Modules S) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((N.restrictionComp φ ψ).inv.app M).val.app U x = x := by
  have h := congrArg (fun k ↦ k.val.app U x) ((N.restrictionComp φ ψ).app M).inv_hom_id
  change ((N.restrictionComp φ ψ).hom.app M).val.app U
    (((N.restrictionComp φ ψ).inv.app M).val.app U x) = x at h
  rwa [N.restrictionComp_sections] at h

attribute [local irreducible] tensorPure restrictionExtensionTensorIso cancellationSheafIso

private noncomputable def underlyingReductionIso {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S)
    [IsIso ((N.ordinaryAdjunction φ).counit.app
      ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))))]
    (M : Modules B) :
    (restriction (φ ≫ ψ)).obj ((p (φ ≫ ψ)).ordinary.obj ((restriction φ).obj M)) ≅
      (restriction (φ ≫ ψ)).obj ((p ψ).ordinary.obj M) := by
  let := monoidalCategory R
  let := monoidalCategory B
  let K := (restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))
  let μ : changeOfRings φ ((restriction φ).obj K) ⟶ K :=
    eqToHom ((p φ).obj_eq ((restriction φ).obj K)).symm ≫
      (N.ordinaryAdjunction φ).counit.app K
  letI : IsIso μ := by dsimp [μ]; infer_instance
  exact restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M) ≪≫
    tensorIso (Iso.refl _) ((N.restrictionComp φ ψ).app
      (unit (derivedChangeRingIndependentCoefficients J S))).symm ≪≫
    (cancellationSheafIso φ M ((restriction φ).obj K)).symm ≪≫
    (restriction φ).mapIso (tensorIso (Iso.refl M) (asIso μ)) ≪≫
    (restriction φ).mapIso (restrictionExtensionTensorIso p ψ M).symm ≪≫
    (N.restrictionComp φ ψ).app ((p ψ).ordinary.obj M)

private theorem underlyingReductionIso_hom {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S)
    [IsIso ((N.ordinaryAdjunction φ).counit.app
      ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))))]
    (M : Modules B) :
    let K := (restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))
    let μ : changeOfRings φ ((restriction φ).obj K) ⟶ K :=
      eqToHom ((p φ).obj_eq ((restriction φ).obj K)).symm ≫
        (N.ordinaryAdjunction φ).counit.app K
    (underlyingReductionIso p N φ ψ M).hom =
      (restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).hom ≫
        (monoidalCategory R).tensorHom (𝟙 _) ((N.restrictionComp φ ψ).inv.app
          (unit (derivedChangeRingIndependentCoefficients J S))) ≫
        (cancellationSheafIso φ M ((restriction φ).obj K)).inv ≫
        (restriction φ).map ((monoidalCategory B).tensorHom (𝟙 M) μ) ≫
        (restriction φ).map (restrictionExtensionTensorIso p ψ M).inv ≫
        (N.restrictionComp φ ψ).hom.app ((p ψ).ordinary.obj M) := by
  rfl

attribute [local irreducible] underlyingReductionIso

private theorem underlyingReductionIso_pure {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S)
    [IsIso ((N.ordinaryAdjunction φ).counit.app
      ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))))]
    (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (underlyingReductionIso p N φ ψ M).hom.val.app U
      (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
        sectionTensor (p ψ) M U s x := by
  let := monoidalCategory R
  let := monoidalCategory B
  let K := (restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))
  let μ : changeOfRings φ ((restriction φ).obj K) ⟶ K :=
    eqToHom ((p φ).obj_eq ((restriction φ).obj K)).symm ≫
      (N.ordinaryAdjunction φ).counit.app K
  have hμ : μ.val.app U (pure φ ((restriction φ).obj K) U 1 s) = s := by
    have h := congrArg (fun k ↦ k.val.app U s)
      ((N.ordinaryAdjunction φ).right_triangle_components K)
    change ((N.ordinaryAdjunction φ).counit.app K).val.app U
      (((N.ordinaryAdjunction φ).unit.app ((restriction φ).obj K)).val.app U s) = s at h
    rwa [N.ordinary_unit] at h
  have hd := congrArg (fun y ↦
    (restrictionExtensionTensorIso p ψ M).inv.val.app U y)
      (restrictionExtensionTensorIso_pure p ψ M U s x)
  have hh := congrArg (fun k ↦ k.val.app U (sectionTensor (p ψ) M U s x))
    (restrictionExtensionTensorIso p ψ M).hom_inv_id
  change (restrictionExtensionTensorIso p ψ M).inv.val.app U
    ((restrictionExtensionTensorIso p ψ M).hom.val.app U
      (sectionTensor (p ψ) M U s x)) = sectionTensor (p ψ) M U s x at hh
  rw [hh] at hd
  rw [underlyingReductionIso_hom]
  change ((N.restrictionComp φ ψ).hom.app ((p ψ).ordinary.obj M)).val.app U
    ((restrictionExtensionTensorIso p ψ M).inv.val.app U
      ((𝟙 M ⊗ₘ μ).val.app U
        ((cancellationSheafIso φ M ((restriction φ).obj K)).inv.val.app U
          ((𝟙 ((restriction φ).obj M) ⊗ₘ
            ((N.restrictionComp φ ψ).inv.app
              (unit (derivedChangeRingIndependentCoefficients J S)))).val.app U
            ((restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).hom.val.app U
              (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x)))))) = _
  erw [restrictionExtensionTensorIso_pure]
  erw [tensorPure_map]
  dsimp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  erw [restrictionComp_inv_section p N φ ψ
    (unit (derivedChangeRingIndependentCoefficients J S)) U s]
  erw [cancellationSheafIso_inv_pure]
  erw [tensorPure_map]
  erw [hμ]
  erw [← hd]
  erw [N.restrictionComp_sections]

private theorem ordinaryReductionMap_isIso {S : Sheaf J CommRingCat.{r}}
    (ψ : B ⟶ S)
    [IsIso ((N.ordinaryAdjunction φ).counit.app
      ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))))] :
    IsIso (ordinaryReductionMap p N φ ψ) := by
  have : (restriction (φ ≫ ψ)).ReflectsIsomorphisms := by
    have : (restriction (φ ≫ ψ) ⋙
        toSheaf (derivedChangeRingIndependentCoefficients J R)).ReflectsIsomorphisms :=
      inferInstanceAs (toSheaf (derivedChangeRingIndependentCoefficients J S)).ReflectsIsomorphisms
    exact reflectsIsomorphisms_of_comp _
      (toSheaf (derivedChangeRingIndependentCoefficients J R))
  have hi (M : Modules B) : IsIso ((ordinaryReductionMap p N φ ψ).app M) := by
    have he : (restriction (φ ≫ ψ)).map ((ordinaryReductionMap p N φ ψ).app M) =
        (underlyingReductionIso p N φ ψ M).hom := by
      apply (cancel_epi (restrictionExtensionTensorIso p (φ ≫ ψ)
        ((restriction φ).obj M)).inv).mp
      apply tensorPure_hom_ext R ((restriction φ).obj M)
        ((restriction (φ ≫ ψ)).obj (unit (derivedChangeRingIndependentCoefficients J S))) _
      intro U x s
      change S.obj.obj U at s
      change M.val.obj U at x
      have hd := congrArg (fun y ↦
        (restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).inv.val.app U y)
          (restrictionExtensionTensorIso_pure p (φ ≫ ψ) ((restriction φ).obj M) U s x)
      have hh := congrArg (fun k ↦ k.val.app U
        (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x))
          (restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).hom_inv_id
      change (restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).inv.val.app U
        ((restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).hom.val.app U
          (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x)) =
            sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x at hh
      rw [hh] at hd
      change ((ordinaryReductionMap p N φ ψ).app M).val.app U
        ((restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).inv.val.app U
          (tensorPure R ((restriction φ).obj M) _ U x s)) =
        (underlyingReductionIso p N φ ψ M).hom.val.app U
          ((restrictionExtensionTensorIso p (φ ≫ ψ) ((restriction φ).obj M)).inv.val.app U
            (tensorPure R ((restriction φ).obj M) _ U x s))
      erw [← hd, ordinaryReductionMap_pure, underlyingReductionIso_pure]
    have : IsIso ((restriction (φ ≫ ψ)).map
        ((ordinaryReductionMap p N φ ψ).app M)) := by rw [he]; infer_instance
    exact isIso_of_reflects_iso _ (restriction (φ ≫ ψ))
  have := hi
  exact NatIso.isIso_of_isIso_app _

end Construction

/-- If the multiplication B tensor_R S to S is invertible, the balanced map
S tensor_R Res(M) to S tensor_B M is a natural isomorphism. Flatness is unnecessary
for this ordinary assertion.

Source: Stacks Project, Modules on Sites, Tags 03EK and 05V4, displayed cancellation.
(auxiliary; not a blueprint node).

Proof: restriction of scalars commutes with module sheafification, since both
underlying abelian sheafifications coincide. The sectionwise balanced isomorphism
Res(M) tensor_R Res(S) = Res(M tensor_B (B tensor_R Res(S))) therefore descends
by sheafification. Tensor the assumed multiplication isomorphism with M and
compose with this cancellation. Identify the restrictions of scalar extensions
with tensoring by the restricted coefficient unit; these identifications are
identities on pure tensors. Restriction reflects isomorphisms, so the canonical
S-linear balanced map is invertible. Its formula sends s tensor x to s tensor x:
the inverse cancellation inserts 1 and multiplication sends 1 tensor s to s.
All these maps commute with module morphisms. They therefore assemble into a
natural isomorphism, with the displayed formula after transport by Presentation.obj_eq.
The argument uses no stalks, no flatness, and applies to zero modules and zero rings. -/
theorem ordinary_flatCoefficientComparison
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (N : Normalization p) {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (ψ : B ⟶ S)
    (hμ : IsIso ((N.ordinaryAdjunction φ).counit.app
      ((restriction ψ).obj (unit (derivedChangeRingIndependentCoefficients J S))))) :
    ∃ o : restriction φ ⋙ (p (φ ≫ ψ)).ordinary ≅ (p ψ).ordinary,
      ∀ (M : Modules B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        (o.hom.app M).val.app U
          (sectionTensor (p (φ ≫ ψ)) ((restriction φ).obj M) U s x) =
            sectionTensor (p ψ) M U s x := by
  have := hμ
  have := ordinaryReductionMap_isIso p N φ ψ
  exact ⟨asIso (ordinaryReductionMap p N φ ψ), ordinaryReductionMap_pure p N φ ψ⟩
end SheafOfModules
