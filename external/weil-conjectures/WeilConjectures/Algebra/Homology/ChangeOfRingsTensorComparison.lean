/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Comparing restricted scalar extension with the sheaf tensor product

Source: Stacks Project, Modules on Sites, Tag 03EK; Tag 06YY.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

-- Step 1: the same tensor abelian group, with the two scalar actions identified.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionTensorIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (M : SheafOfModules.{u} (𝓡 O))
    (X : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X ≅
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X := by
  let e : (((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X) ≃ₗ[O.obj.obj X]
      ((((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change TensorProduct (O.obj.obj X)
          ((ModuleCat.restrictScalars (φ.hom.app X).hom).obj
            (ModuleCat.of _ (O'.obj.obj X))) (M.val.obj X) at x
        induction x using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy }
  exact e.toModuleIso

set_option backward.isDefEq.respectTransparency false in
private noncomputable def presheafTensorIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (M : SheafOfModules.{u} (𝓡 O)) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M) ≅
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val :=
  PresheafOfModules.isoMk (sectionTensorIso φ M) (by
    intro X Y f
    ext x
    change TensorProduct (O.obj.obj X)
      ((ModuleCat.restrictScalars (φ.hom.app X).hom).obj
        (ModuleCat.of _ (O'.obj.obj X))) (M.val.obj X) at x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      change changeOfRingsMap φ M f (s ⊗ₜ m) = _
      rw [show changeOfRingsMap φ M f (s ⊗ₜ m) = _ from
        Classical.choose_spec (exists_changeOfRingsMap φ M f) s m]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

private noncomputable def changePresheafHom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
  { app := fun X ↦ (ModuleCat.extendScalars (φ.hom.app X).hom).map (a.val.app X)
    naturality := changeOfRingsHom_naturality φ M a }

set_option backward.isDefEq.respectTransparency false in
private lemma presheafTensorIso_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map
        (changePresheafHom φ a) ≫ (presheafTensorIso φ N).hom =
      (presheafTensorIso φ M).hom ≫
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit (𝓡 O'))).val ◁ a.val := by
  ext X x
  change TensorProduct (O.obj.obj X)
    ((ModuleCat.restrictScalars (φ.hom.app X).hom).obj
      (ModuleCat.of _ (O'.obj.obj X))) (M.val.obj X) at x
  induction x using TensorProduct.inductionOn with
  | tmul s m => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

-- Step 2: extend the restricted sheafification unit by the module adjunction.
private noncomputable def restrictionSheafificationHom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (P : PresheafOfModules.{u} (𝓡 O').obj) :
    (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).obj
      ((PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj P) ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        ((PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 O).obj)).symm
    ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O').obj)).unit.app P))

set_option backward.isDefEq.respectTransparency false in
private lemma restrictionSheafificationHom_toSheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (P : PresheafOfModules.{u} (𝓡 O').obj) :
    (toSheaf (𝓡 O)).map (restrictionSheafificationHom φ P) =
      𝟙 ((PresheafOfModules.toPresheaf (𝓡 O').obj ⋙
        presheafToSheaf J AddCommGrpCat).obj P) := by
  rw [restrictionSheafificationHom,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictionSheafificationIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (P : PresheafOfModules.{u} (𝓡 O').obj) :
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        ((PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)).obj P) ≅
    (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).obj
      ((PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj P) := by
  have : IsIso (restrictionSheafificationHom φ P) := by
    have : IsIso ((toSheaf (𝓡 O)).map (restrictionSheafificationHom φ P)) := by
      rw [restrictionSheafificationHom_toSheaf]
      exact IsIso.id _
    exact isIso_of_reflects_iso _ (toSheaf (𝓡 O))
  exact (asIso (restrictionSheafificationHom φ P)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma restrictionSheafificationIso_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    {P Q : PresheafOfModules.{u} (𝓡 O').obj} (a : P ⟶ Q) :
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
      ((PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)).map a) ≫
        (restrictionSheafificationIso φ Q).hom =
    (restrictionSheafificationIso φ P).hom ≫
      (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).map
        ((PresheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map a) := by
  apply (cancel_mono (restrictionSheafificationIso φ Q).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (restrictionSheafificationIso φ P).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply (toSheaf (𝓡 O)).map_injective
  simp only [Functor.map_comp]
  change (toSheaf (𝓡 O)).map (restrictionSheafificationHom φ P) ≫ _ =
    _ ≫ (toSheaf (𝓡 O)).map (restrictionSheafificationHom φ Q)
  rw [restrictionSheafificationHom_toSheaf, restrictionSheafificationHom_toSheaf]
  change (𝟙 _) ≫
      (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf (𝓡 O').obj).map a) =
    (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf (𝓡 O').obj).map a) ≫ (𝟙 _)
  simp only [Category.comp_id, Category.id_comp]

-- Step 3: naturality of the existing tensor comparison, from the counit and tensorator.
set_option backward.isDefEq.respectTransparency false in
private lemma tensorComparison_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O : Sheaf J CommRingCat.{u}}
    (S : SheafOfModules.{u} (𝓡 O)) {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N) :
    letI := monoidalCategory O
    (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).map (S.val ◁ a.val) ≫
      (tensorObjIsoSheafification S N).inv =
    (tensorObjIsoSheafification S M).inv ≫ S ◁ a := by
  let := monoidalCategory O
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  let ε : forget (𝓡 O) ⋙ A ≅ 𝟭 _ :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O).obj)).counit
  let c (M : SheafOfModules.{u} (𝓡 O)) : A.obj M.val ≅ M := ε.app M
  apply (cancel_mono (tensorObjIsoSheafification S N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (tensorObjIsoSheafification S M).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change ((c S).inv ⊗ₘ (c M).inv) ≫
      Functor.LaxMonoidal.μ A S.val M.val ≫ A.map (S.val ◁ a.val) =
    S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) ≫
      Functor.LaxMonoidal.μ A S.val N.val
  rw [← Functor.LaxMonoidal.μ_natural_right]
  have hn : (c M).inv ≫ A.map a.val = a ≫ (c N).inv :=
    (ε.inv.naturality a).symm
  have h : ((c S).inv ⊗ₘ (c M).inv) ≫
      (A.obj S.val ◁ A.map a.val) =
      S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) := by
    calc
      _ = (c S).inv ⊗ₘ ((c M).inv ≫ A.map a.val) := by
        simpa only [Category.comp_id, id_tensorHom] using
          (tensorHom_comp_tensorHom (c S).inv (c M).inv
            (𝟙 (A.obj S.val)) (A.map a.val))
      _ = (c S).inv ⊗ₘ (a ≫ (c N).inv) :=
        congrArg (fun f ↦ (c S).inv ⊗ₘ f) hn
      _ = _ := by
        simpa only [Category.id_comp, id_tensorHom] using
          (tensorHom_comp_tensorHom (𝟙 S) a (c S).inv (c N).inv).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f ↦ f ≫ Functor.LaxMonoidal.μ A S.val N.val) h) |>.trans
      (Category.assoc _ _ _)

/-- Source: Stacks Project, Tag 03EK and Tag 06YY, degree-zero tensor comparison.

Proof: Put U = restriction along φ and S = U(O'). Before sheafification the
identity on pure tensors identifies the restricted sectionwise scalar extension
O'(V) tensor over O(V) M(V) with the sectionwise tensor of S and M. It respects
restrictions because both constructions restrict each tensor factor, and respects
module morphisms because both apply id tensor a. Restriction of scalars commutes
with sheafification: the underlying abelian presheaf and its associated sheaf are
unchanged, and the induced O action is restriction of the induced O' action.
Thus these presheaf identifications sheafify to the asserted isomorphisms.
The counit at the already-sheaf module S and the monoidal localization comparison
identify the resulting sheafification with S tensor M. Naturality survives each
comparison and sheafification, giving the displayed equation for every a.
This uses no flatness; the identity on tensors also covers zero rings and modules.
(blueprint: lem-pur-change-of-rings-tensor-comparison) -/
theorem exists_changeOfRings_tensor_comparison
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O') :
    letI := monoidalCategory O
    let U := restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
    let S := U.obj (unit (𝓡 O'))
    ∃ e : ∀ M : SheafOfModules.{u} (𝓡 O), U.obj (changeOfRings φ M) ≅ S ⊗ M,
      ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
        U.map (changeOfRingsHom φ M a) ≫ (e N).hom = (e M).hom ≫ S ◁ a := by
  let := monoidalCategory O
  let U := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let S := U.obj (unit (𝓡 O'))
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  let e (M : SheafOfModules.{u} (𝓡 O)) : U.obj (changeOfRings φ M) ≅ S ⊗ M :=
    restrictionSheafificationIso φ (changeOfRingsPresheaf φ M) ≪≫
      A.mapIso (presheafTensorIso φ M) ≪≫ (tensorObjIsoSheafification S M).symm
  refine ⟨e, ?_⟩
  intro M N a
  have hr := restrictionSheafificationIso_naturality φ (changePresheafHom φ a)
  have hp := congrArg A.map (presheafTensorIso_naturality φ a)
  simp only [Functor.map_comp] at hp
  have ht := tensorComparison_naturality S a
  change U.map (changeOfRingsHom φ M a) ≫ (e N).hom = (e M).hom ≫ S ◁ a
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change U.map ((PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)).map
      (changePresheafHom φ a)) ≫ _ = _
  simp only [Category.assoc]
  rw [reassoc_of% hr, reassoc_of% hp, ht]

end SheafOfModules
