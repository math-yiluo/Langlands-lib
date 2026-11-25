/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransition
public import WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification

/-!
# Change of rings as a tensor product, and its transition maps

For a morphism `φ : R ⟶ S` of sheaves of commutative rings and a sheaf of `R`-modules `M`,
the change of rings `S ⊗_R M`, regarded as an `R`-module, is the sheaf tensor product
`M ⊗_R S`. Under this identification the transition `s ⊗ m ↦ β s ⊗ m` between changes of
rings is the tensor product of `M` with the coefficient map.

Source: Stacks Project, Tag 03EK.
-/

public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ChangeOfRings

namespace SheafOfModules

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

open RestrictedTensorProof

attribute [local implicit_reducible] SheafOfModules.restrictScalars SheafOfModules.unit
  CategoryTheory.sheafCompose siteSheafTensorRight

private theorem presentation_hom
    (M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (tensorRightPresentation R N).hom.app M = (tensorObjIsoSheafification M N).hom := by
  have hi : ((tensorRightPresentation R N).app M).inv =
      (tensorObjIsoSheafification M N).inv := by
    dsimp only [tensorRightPresentation, Iso.trans_inv, NatTrans.comp_app,
      Functor.mapIso_inv, Iso.symm_inv, NatIso.ofComponents_inv_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.app_hom,
      NatIso.ofComponents_hom_app]
    simp only [tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv,
      tensorIso_hom, tensorHom_def]
    rfl
  exact congrArg Iso.hom (Iso.ext_inv hi)

/-- The change of rings of `M`, as a module over the source ring, is the sheaf tensor product of
`M` with the target ring. Source: Stacks Project, Tag 03EK. -/
def changeOfRingsTensorIso (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M ⊗ restrictedTensorCoefficient φ ≅
      (restrictedTensorScalars φ).obj (changeOfRings φ M) :=
  (siteSheafTensorRightIso R (restrictedTensorCoefficient φ)).symm.app M ≪≫
    (swapSheafIso φ M).symm

attribute [local irreducible] changeOfRingsTensorIso swapSheafIso
  siteSheafTensorRightIso tensorObjIsoSheafification

/-- The tensor identification of a change of rings on pure tensors. -/
theorem changeOfRingsTensorIso_hom_tmul (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (x : M.val.obj U) (s : S.obj.obj U) :
    (changeOfRingsTensorIso φ M).hom.val.app U
        (CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s) =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) := by
  have hswap := swapSheafIso_tmul φ M U s x
  apply (ConcreteCategory.bijective_of_isIso
    (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U).map (swapSheafIso φ M).hom))).1
  change ((changeOfRingsTensorIso φ M).hom ≫ (swapSheafIso φ M).hom).val.app U
      (CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s) = _
  simp only [changeOfRingsTensorIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change ((siteSheafTensorRightIso R (restrictedTensorCoefficient φ)).symm.app M).hom.val.app U
      (CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s) =
    (swapSheafIso φ M).hom.val.app U
      ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  conv_rhs => rw [hswap]
  let a := PresheafOfModules.sheafification (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
  let N := restrictedTensorCoefficient φ
  have he : (tensorObjIsoSheafification M N).inv ≫
      ((siteSheafTensorRightIso R N).symm.app M).hom =
        a.map ((siteTensorRightIso R N.val).inv.app M.val) := by
    simp only [siteSheafTensorRightIso, Iso.app_hom, NatTrans.comp_app,
      Iso.symm_hom, Iso.trans_inv,
      Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    rw [presentation_hom, Iso.inv_hom_id_assoc]
    rfl
  change ((adj.unit.app (M.val ⊗ N.val) ≫
    ((tensorObjIsoSheafification M N).inv ≫
      ((siteSheafTensorRightIso R N).symm.app M).hom).val).app U) (x ⊗ₜ[R.obj.obj U] s) = _
  rw [he]
  have hn := congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] s))
    (adj.unit.naturality ((siteTensorRightIso R N.val).inv.app M.val))
  exact hn.symm

/-- The inverse tensor identification of a change of rings on sheafified pure tensors. -/
theorem changeOfRingsTensorIso_inv_tmul (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (x : M.val.obj U) (s : S.obj.obj U) :
    (changeOfRingsTensorIso φ M).inv.val.app U
      ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s := by
  have h := congrArg ((changeOfRingsTensorIso φ M).inv.val.app U)
    (changeOfRingsTensorIso_hom_tmul φ M U x s)
  simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← comp_val, Iso.hom_inv_id, id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using h.symm

/-- Under the tensor identification, the transition `s ⊗ m ↦ β s ⊗ m` between changes of rings
is the tensor product of `M` with the coefficient map. -/
theorem changeOfRingsTensorIso_inv_transition {R₁ R₂ R₃ : Sheaf J CommRingCat.{r}}
    (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) (γ : R₁ ⟶ R₃) (h : α ≫ β = γ)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁))
    (b : restrictedTensorCoefficient α ⟶ restrictedTensorCoefficient γ)
    (hb : ∀ (U : Cᵒᵖ) (s : R₂.obj.obj U), b.val.app U s = β.hom.app U s)
    (U : Cᵒᵖ) (y : (changeOfRings α M).val.obj U) :
    (M ◁ b).val.app U ((changeOfRingsTensorIso α M).inv.val.app U y) =
      (changeOfRingsTensorIso γ M).inv.val.app U
        ((changeOfRingsTransition α β γ h M).val.app U y) := by
  let F₁ : (toSheaf _).obj ((restrictedTensorScalars α).obj (changeOfRings α M)) ⟶
      (toSheaf _).obj (M ⊗ restrictedTensorCoefficient γ) :=
    (toSheaf _).map ((changeOfRingsTensorIso α M).inv ≫ (M ◁ b))
  let F₂ : (toSheaf _).obj ((restrictedTensorScalars α).obj (changeOfRings α M)) ⟶
      (toSheaf _).obj (M ⊗ restrictedTensorCoefficient γ) :=
    ⟨(PresheafOfModules.toPresheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₂).obj).map
        (changeOfRingsTransition α β γ h M).val ≫
      (PresheafOfModules.toPresheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁).obj).map
        (changeOfRingsTensorIso γ M).inv.val⟩
  have hF : F₁ = F₂ := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ ((toSheaf _).obj (M ⊗ restrictedTensorCoefficient γ)).property
    ext V p
    change ((M ◁ b).val.app V ((changeOfRingsTensorIso α M).inv.val.app V
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app V p))) =
      (changeOfRingsTensorIso γ M).inv.val.app V ((changeOfRingsTransition α β γ h M).val.app V
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app V p))
    induction p using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      rw [changeOfRingsTensorIso_inv_tmul, changeOfRingsTransition_tmul,
        changeOfRingsTensorIso_inv_tmul, ← MonoidalCategory.id_tensorHom,
        CochainPullback.moduleTmul_map, hb]
      rfl
  exact congrArg (fun k ↦ k.hom.app U y) hF

/-- The tensor identification of a change of rings is natural. -/
theorem changeOfRingsTensorIso_inv_naturality (φ : R ⟶ S)
    {M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M ⟶ N) (U : Cᵒᵖ) (y : (changeOfRings φ M).val.obj U) :
    (a ▷ restrictedTensorCoefficient φ).val.app U
        ((changeOfRingsTensorIso φ M).inv.val.app U y) =
      (changeOfRingsTensorIso φ N).inv.val.app U ((changeOfRingsHom φ M a).val.app U y) := by
  let F₁ : (toSheaf _).obj ((restrictedTensorScalars φ).obj (changeOfRings φ M)) ⟶
      (toSheaf _).obj (N ⊗ restrictedTensorCoefficient φ) :=
    (toSheaf _).map ((changeOfRingsTensorIso φ M).inv ≫ (a ▷ restrictedTensorCoefficient φ))
  let F₂ : (toSheaf _).obj ((restrictedTensorScalars φ).obj (changeOfRings φ M)) ⟶
      (toSheaf _).obj (N ⊗ restrictedTensorCoefficient φ) :=
    ⟨(PresheafOfModules.toPresheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj).map
        (changeOfRingsHom φ M a).val ≫
      (PresheafOfModules.toPresheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj).map
        (changeOfRingsTensorIso φ N).inv.val⟩
  have hF : F₁ = F₂ := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ ((toSheaf _).obj (N ⊗ restrictedTensorCoefficient φ)).property
    ext V p
    change ((a ▷ restrictedTensorCoefficient φ).val.app V
        ((changeOfRingsTensorIso φ M).inv.val.app V
        ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V p))) =
      (changeOfRingsTensorIso φ N).inv.val.app V ((changeOfRingsHom φ M a).val.app V
        ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V p))
    induction p using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      rw [changeOfRingsTensorIso_inv_tmul, changeOfRingsHom_toSheafify]
      erw [ModuleCat.ExtendScalars.map_tmul]
      rw [changeOfRingsTensorIso_inv_tmul, ← MonoidalCategory.tensorHom_id,
        CochainPullback.moduleTmul_map]
      rfl
  exact congrArg (fun k ↦ k.hom.app U y) hF

/-- Change of rings, regarded as a module over the source ring, is the tensor product with the
target ring, naturally in the module, for any functor computing change of rings. -/
def changeOfRingsTensorNatIso (φ : R ⟶ S)
    (E : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom φ M a ≫ eqToHom (h N).symm) :
    E ⋙ restrictedTensorScalars φ ≅ tensorRight (restrictedTensorCoefficient φ) :=
  NatIso.ofComponents (fun M ↦ (restrictedTensorScalars φ).mapIso (eqToIso (h M)) ≪≫
      (changeOfRingsTensorIso φ M).symm) (by
    intro M N a
    change (restrictedTensorScalars φ).map (E.map a) ≫
        ((restrictedTensorScalars φ).map (eqToHom (h N)) ≫ (changeOfRingsTensorIso φ N).inv) =
      ((restrictedTensorScalars φ).map (eqToHom (h M)) ≫ (changeOfRingsTensorIso φ M).inv) ≫
        (a ▷ restrictedTensorCoefficient φ)
    rw [hm]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    congr 1
    ext U y
    exact (changeOfRingsTensorIso_inv_naturality φ a U y).symm)

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
/-- Transport along an equality of module sheaves and back is the identity on sections. -/
theorem eqToHom_val_app_eqToHom_symm {R₀ : Sheaf J RingCat.{r}}
    {A B : SheafOfModules.{r} R₀} (h : A = B) (U : Cᵒᵖ) (z : B.val.obj U) :
    (eqToHom h).val.app U ((eqToHom h.symm).val.app U z) = z := by
  subst h
  rfl

/-- Under the tensor identifications of two functors computing changes of rings, the transition
`s ⊗ m ↦ β s ⊗ m` is the tensor product of `M` with the coefficient map. -/
theorem changeOfRingsTensorNatIso_transition {R₁ R₂ R₃ : Sheaf J CommRingCat.{r}}
    (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) (γ : R₁ ⟶ R₃) (h : α ≫ β = γ)
    {E₂ : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₂)}
    {E₃ : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₃)}
    (h₂ : ∀ M, E₂.obj M = changeOfRings α M)
    (hm₂ : ∀ {M N} (a : M ⟶ N),
      E₂.map a = eqToHom (h₂ M) ≫ changeOfRingsHom α M a ≫ eqToHom (h₂ N).symm)
    (h₃ : ∀ M, E₃.obj M = changeOfRings γ M)
    (hm₃ : ∀ {M N} (a : M ⟶ N),
      E₃.map a = eqToHom (h₃ M) ≫ changeOfRingsHom γ M a ≫ eqToHom (h₃ N).symm)
    (b : restrictedTensorCoefficient α ⟶ restrictedTensorCoefficient γ)
    (hb : ∀ (U : Cᵒᵖ) (s : R₂.obj.obj U), b.val.app U s = β.hom.app U s)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁))
    (e : (restrictedTensorScalars α).obj ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map β)).obj (E₃.obj M)) ≅
      (restrictedTensorScalars γ).obj (E₃.obj M))
    (he : ∀ (U : Cᵒᵖ) (y : (E₃.obj M).val.obj U), e.hom.val.app U y = y) :
    (restrictedTensorScalars α).map
        ((changeOfRingsTransitionOfEq α β γ h h₂ hm₂ h₃ hm₃).app M) ≫ e.hom ≫
        (changeOfRingsTensorNatIso γ E₃ h₃ hm₃).hom.app M =
      (changeOfRingsTensorNatIso α E₂ h₂ hm₂).hom.app M ≫ (M ◁ b) := by
  ext U y
  change (changeOfRingsTensorIso γ M).inv.val.app U ((eqToHom (h₃ M)).val.app U
      (e.hom.val.app U ((eqToHom (h₃ M).symm).val.app U
        ((changeOfRingsTransition α β γ h M).val.app U ((eqToHom (h₂ M)).val.app U y))))) =
    (M ◁ b).val.app U ((changeOfRingsTensorIso α M).inv.val.app U ((eqToHom (h₂ M)).val.app U y))
  rw [he, eqToHom_val_app_eqToHom_symm, changeOfRingsTensorIso_inv_transition α β γ h M b hb]

end SheafOfModules
