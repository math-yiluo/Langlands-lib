/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InvertibleTensorScalarExtensionDefinitions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-!
# Binary scalar-extension comparisons

Source: Stacks Project, Tag 03EK.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u m

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

set_option hygiene false in
local notation:max "Mod" R:arg =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation:max "𝒪" R:arg => unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation:max "𝒯" N:arg P:arg => (siteSheafTensorRight P).obj N

/-- Sectionwise multiplication identifies scalar extension of the unit with the target unit.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarExtensionUnitRawIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    changeOfRingsPresheafOfUniverses α (𝒪 R) ≅ (𝒪 S).val :=
  PresheafOfModules.isoMk (fun U ↦ by
    let := (α.hom.app U).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid
      (R.obj.obj U) (S.obj.obj U) (S.obj.obj U)).toModuleIso) (by
    intro U V i
    let := (α.hom.app U).hom.toAlgebra
    let := (α.hom.app V).hom.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro a
    change (TensorProduct.AlgebraTensorModule.rid
        (R.obj.obj V) (S.obj.obj V) (S.obj.obj V))
        (changeOfRingsMapOfUniverses α (𝒪 R) i
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] a)) = _
    rw [changeOfRingsMap_tmulOfUniverses]
    change (α.hom.app V (R.obj.map i a)) * S.obj.map i 1 =
      S.obj.map i ((α.hom.app U a) * 1)
    simp only [map_one, mul_one]
    exact ConcreteCategory.congr_hom (α.hom.naturality i) a)

/-- Sheafify the explicit multiplication isomorphism and compose with the counit.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarExtensionUnitIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    changeOfRingsOfUniverses α (𝒪 R) ≅ 𝒪 S :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).mapIso
      (scalarExtensionUnitRawIso α) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).counit).app (𝒪 S)

/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarTensorLeftUnitRawIso (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    siteTensorPresheaf (𝒪 R).val N.val ≅ N.val :=
  PresheafOfModules.isoMk (fun U ↦ (TensorProduct.lid (R.obj.obj U) (N.val.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a x
      exact (N.val.map_smul i a x).symm)

/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarTensorLeftUnitor (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    𝒯 (𝒪 R) N ≅ N :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).mapIso
      (scalarTensorLeftUnitRawIso R N) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).counit).app N

/-- The tensor unit comparison sends a pure tensor to scalar multiplication.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: the sheafification adjunction identifies the comparison with sectionwise multiplication. -/
theorem scalarTensorLeftUnitor_tmul (R : Sheaf J CommRingCat.{u}) (N : Mod R)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U) :
    ((scalarTensorLeftUnitor R N).hom.val.app U) (siteSheafTensorTmul (𝒪 R) N U a x) =
      a • x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h : adj.homEquiv _ _ (scalarTensorLeftUnitor R N).hom =
      (scalarTensorLeftUnitRawIso R N).hom := by
    change adj.homEquiv _ _ (_ ≫ adj.counit.app N) = _
    simp only [Functor.mapIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  exact congrArg (fun f ↦ f.app U (a ⊗ₜ[R.obj.obj U] x)) h

/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarTensorRightUnitRawIso (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    siteTensorPresheaf N.val (𝒪 R).val ≅ N.val :=
  PresheafOfModules.isoMk (fun U ↦ (TensorProduct.rid (R.obj.obj U) (N.val.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x a
      exact (N.val.map_smul i a x).symm)

/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarTensorRightUnitor (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    𝒯 N (𝒪 R) ≅ N :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).mapIso
      (scalarTensorRightUnitRawIso R N) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).counit).app N

/-- The tensor unit comparison sends a pure tensor to scalar multiplication.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: the sheafification adjunction identifies the comparison with sectionwise multiplication. -/
theorem scalarTensorRightUnitor_tmul (R : Sheaf J CommRingCat.{u}) (N : Mod R)
    (U : Cᵒᵖ) (x : N.val.obj U) (a : R.obj.obj U) :
    ((scalarTensorRightUnitor R N).hom.val.app U) (siteSheafTensorTmul N (𝒪 R) U x a) =
      a • x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h : adj.homEquiv _ _ (scalarTensorRightUnitor R N).hom =
      (scalarTensorRightUnitRawIso R N).hom := by
    change adj.homEquiv _ _ (_ ≫ adj.counit.app N) = _
    simp only [Functor.mapIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  exact congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] a)) h

/-- scalarTensorSwapRawIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node). -/
noncomputable def scalarTensorSwapRawIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorPresheaf P Q ≅ siteTensorPresheaf Q P :=
  PresheafOfModules.isoMk
    (fun U ↦ (TensorProduct.comm (R.obj.obj U) (P.obj U) (Q.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl)

/-- scalarTensorAssocRawIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node). -/
noncomputable def scalarTensorAssocRawIso {R : Sheaf J CommRingCat.{u}}
    (P Q Z : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorPresheaf (siteTensorPresheaf P Q) Z ≅
      siteTensorPresheaf P (siteTensorPresheaf Q Z) :=
  PresheafOfModules.isoMk
    (fun U ↦ (TensorProduct.assoc (R.obj.obj U) (P.obj U) (Q.obj U) (Z.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro xy z
      induction xy using TensorProduct.inductionOn with
      | add xy xy' h h' => simp only [map_add, TensorProduct.add_tmul, h, h']
      | tmul x y => rfl)

/-- scalarSheafificationUnit for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node). -/
noncomputable def scalarSheafificationUnit
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app P

/-- scalarSheafificationUnit locallyInjective for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
instance scalarSheafificationUnit_locallyInjective
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallyInjective J (scalarSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

/-- scalarSheafificationUnit locallySurjective for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
instance scalarSheafificationUnit_locallySurjective
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallySurjective J (scalarSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarSheafification map unit for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarSheafification_map_unit
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    {P Q : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q)
    (U : Cᵒᵖ) (x : P.obj U) :
    (((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map f).val.app U)
      ((scalarSheafificationUnit P).app U x) = (scalarSheafificationUnit Q).app U (f.app U x) := by
  exact (congrArg (fun g ↦ g.app U x)
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.naturality f)).symm

/-- scalarTensorSheafifyFirst isIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifyFirst_isIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    IsIso ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map
        (siteTensorHom (scalarSheafificationUnit P) Q)) := by
  exact PresheafOfModules.sheafification_tensorHom_isIso
    (f := scalarSheafificationUnit P) (N := Q)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property

/-- scalarTensorSheafifyFirstIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node). -/
noncomputable def scalarTensorSheafifyFirstIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf P Q)) ≅
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf
          ((PresheafOfModules.sheafification
            (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val Q)) := by
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let f := siteTensorHom (scalarSheafificationUnit P) Q
  have : IsIso (L.map f) := scalarTensorSheafifyFirst_isIso P Q
  exact asIso (L.map f)

/-- scalarTensorSheafifySecondIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node). -/
noncomputable def scalarTensorSheafifySecondIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf Q P)) ≅
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf Q
          ((PresheafOfModules.sheafification
            (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val)) :=
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  L.mapIso (scalarTensorSwapRawIso Q P) ≪≫
    scalarTensorSheafifyFirstIso P Q ≪≫
      L.mapIso (scalarTensorSwapRawIso (L.obj P).val Q)

/-- scalarTensorAssociatorIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node). -/
noncomputable def scalarTensorAssociatorIso (R : Sheaf J CommRingCat.{u}) (N P Q : Mod R) :
    (siteSheafTensorRight Q).obj ((siteSheafTensorRight P).obj N) ≅ 𝒯 N (𝒯 P Q) :=
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  (scalarTensorSheafifyFirstIso (siteTensorPresheaf N.val P.val) Q.val).symm ≪≫
    L.mapIso (scalarTensorAssocRawIso N.val P.val Q.val) ≪≫
      scalarTensorSheafifySecondIso (siteTensorPresheaf P.val Q.val) N.val

/-- scalarTensorSheafifyFirstIso hom tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifyFirstIso_hom_tmul {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    ((scalarTensorSheafifyFirstIso P Q).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf P Q)).app U (x ⊗ₜ[R.obj.obj U] y)) =
      (scalarSheafificationUnit (siteTensorPresheaf
        ((PresheafOfModules.sheafification
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val Q)).app U
        ((scalarSheafificationUnit P).app U x ⊗ₜ[R.obj.obj U] y) := by
  exact scalarSheafification_map_unit (siteTensorHom (scalarSheafificationUnit P) Q)
    U (x ⊗ₜ[R.obj.obj U] y)

/-- scalarTensorSheafifyFirstIso inv tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifyFirstIso_inv_tmul {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    ((scalarTensorSheafifyFirstIso P Q).inv.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf
        ((PresheafOfModules.sheafification
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val Q)).app U
        ((scalarSheafificationUnit P).app U x ⊗ₜ[R.obj.obj U] y)) =
      ((scalarSheafificationUnit (siteTensorPresheaf P Q)).app U (x ⊗ₜ[R.obj.obj U] y)) := by
  rw [← scalarTensorSheafifyFirstIso_hom_tmul P Q U x y]
  change (((scalarTensorSheafifyFirstIso P Q).hom ≫
    (scalarTensorSheafifyFirstIso P Q).inv).val.app U) _ = _
  rw [Iso.hom_inv_id]
  rfl

/-- scalarTensorSheafifySecondIso hom tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifySecondIso_hom_tmul {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    ((scalarTensorSheafifySecondIso P Q).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf Q P)).app U (y ⊗ₜ[R.obj.obj U] x)) =
      (scalarSheafificationUnit (siteTensorPresheaf Q
        ((PresheafOfModules.sheafification
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val)).app U
        (y ⊗ₜ[R.obj.obj U] (scalarSheafificationUnit P).app U x) := by
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  change ((L.map (scalarTensorSwapRawIso (L.obj P).val Q).hom).val.app U)
    (((scalarTensorSheafifyFirstIso P Q).hom.val.app U)
      (((L.map (scalarTensorSwapRawIso Q P).hom).val.app U)
        ((scalarSheafificationUnit (siteTensorPresheaf Q P)).app U
          (y ⊗ₜ[R.obj.obj U] x)))) = _
  rw [scalarSheafification_map_unit]
  change ((L.map (scalarTensorSwapRawIso (L.obj P).val Q).hom).val.app U)
    (((scalarTensorSheafifyFirstIso P Q).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf P Q)).app U
        (x ⊗ₜ[R.obj.obj U] y))) = _
  rw [scalarTensorSheafifyFirstIso_hom_tmul, scalarSheafification_map_unit]
  rfl

/-- scalarTensorAssociatorIso tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(auxiliary; not a blueprint node).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorAssociatorIso_tmul (R : Sheaf J CommRingCat.{u}) (N P Q : Mod R)
    (U : Cᵒᵖ) (x : N.val.obj U) (y : P.val.obj U) (z : Q.val.obj U) :
    ((scalarTensorAssociatorIso R N P Q).hom.val.app U)
        (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z) =
      siteSheafTensorTmul N (𝒯 P Q) U x (siteSheafTensorTmul P Q U y z) := by
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  change ((scalarTensorSheafifySecondIso (siteTensorPresheaf P.val Q.val) N.val).hom.val.app U)
    (((L.map (scalarTensorAssocRawIso N.val P.val Q.val).hom).val.app U)
      (((scalarTensorSheafifyFirstIso (siteTensorPresheaf N.val P.val) Q.val).inv.val.app U)
        ((scalarSheafificationUnit
          (siteTensorPresheaf (𝒯 N P).val Q.val)).app U
            ((scalarSheafificationUnit (siteTensorPresheaf N.val P.val)).app U
              (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)))) = _
  erw [scalarTensorSheafifyFirstIso_inv_tmul (R := R)
    (siteTensorPresheaf N.val P.val) Q.val U (x ⊗ₜ[R.obj.obj U] y) z]
  rw [scalarSheafification_map_unit]
  change ((scalarTensorSheafifySecondIso (siteTensorPresheaf P.val Q.val) N.val).hom.val.app U)
    ((scalarSheafificationUnit (siteTensorPresheaf N.val
      (siteTensorPresheaf P.val Q.val))).app U (x ⊗ₜ[R.obj.obj U] (y ⊗ₜ[R.obj.obj U] z))) = _
  rw [scalarTensorSheafifySecondIso_hom_tmul]
  rfl

/-- The actual sheaf tensor coherence, constructed without choosing existence witnesses.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarTensorCoherence (R : Sheaf J CommRingCat.{u}) :
    ScalarTensorCoherence R where
  associator := scalarTensorAssociatorIso R
  associator_tmul := scalarTensorAssociatorIso_tmul R
  leftUnitor := scalarTensorLeftUnitor R
  leftUnitor_tmul := scalarTensorLeftUnitor_tmul R
  rightUnitor := scalarTensorRightUnitor R
  rightUnitor_tmul := scalarTensorRightUnitor_tmul R

/-- The binary part of scalar extension, before forming any tensor powers.
Source: Stacks Project, Tag 03EK
(auxiliary; not a blueprint node). -/
structure ScalarExtensionTensorCore
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) where
  tensorComparison : ∀ (N P : Mod R),
    changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N)
  tensor_tmul : ∀ (N P : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U)
      (x : N.val.obj U) (y : P.val.obj U),
    ((tensorComparison N P).hom.val.app U)
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y)
  associator_compat : ∀ (N P Q : Mod R),
    changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).associator N P Q).hom ≫
        (tensorComparison N (𝒯 P Q)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N)
          (tensorComparison P Q).hom =
      (tensorComparison (𝒯 N P) Q).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α Q)).map
          (tensorComparison N P).hom ≫
        ((scalarTensorCoherence S).associator (changeOfRingsOfUniverses α N)
          (changeOfRingsOfUniverses α P) (changeOfRingsOfUniverses α Q)).hom
  leftUnitor_compat : ∀ (N : Mod R),
    (tensorComparison (𝒪 R) N).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).leftUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).leftUnitor N).hom
  rightUnitor_compat : ∀ (N : Mod R),
    (tensorComparison N (𝒪 R)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N) (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).rightUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).rightUnitor N).hom
  tensor_natural : ∀ {N N' P P' : Mod R} (f : N ⟶ N') (g : P ⟶ P'),
    changeOfRingsHomOfUniverses α _
        ((siteSheafTensorRight P).map f ≫ siteSheafTensorSecondMap N' g) ≫
        (tensorComparison N' P').hom =
      (tensorComparison N P).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α P)).map
          (changeOfRingsHomOfUniverses α N f) ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N')
          (changeOfRingsHomOfUniverses α P g)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtension_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_hom_ext
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S)} (f g : changeOfRingsOfUniverses α N ⟶ H)
    (h : ∀ U s x, f.val.app U (scalarExtensionSection α N U s x) =
      g.val.app U (scalarExtensionSection α N U s x)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U 1 x

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_naturality for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_naturality
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsOfUniverses α N).val.map i (scalarExtensionSection α N U s x) =
      scalarExtensionSection α N V (S.obj.map i s) (N.val.map i x) := by
  have h := (PresheafOfModules.naturality_apply
    (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)) i
      (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)).symm
  exact h.trans (congrArg ((scalarSheafificationUnit
    (changeOfRingsPresheafOfUniverses α N)).app V)
      (changeOfRingsMap_tmulOfUniverses α N i s x))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtension_map_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_map_tmul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    {N P : SheafOfModules.{m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)} (f : N ⟶ P)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsHomOfUniverses α N f).val.app U (scalarExtensionSection α N U s x) =
      scalarExtensionSection α P U s (f.val.app U x) := by
  exact scalarSheafification_map_unit
    ({ app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
       naturality := changeOfRingsHom_naturalityOfUniverses α N f } :
      changeOfRingsPresheafOfUniverses α N ⟶ changeOfRingsPresheafOfUniverses α P)
    U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_smul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_smul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s t : S.obj.obj U) (x : N.val.obj U) :
    s • scalarExtensionSection α N U t x = scalarExtensionSection α N U (s * t) x := by
  let η := ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses α N)).app U
  exact (η.hom.map_smul s (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_base_smul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_base_smul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U) (x : N.val.obj U) :
    scalarExtensionSection α N U s (a • x) =
      scalarExtensionSection α N U (s * α.hom.app U a) x := by
  dsimp only [scalarExtensionSection]
  congr 1
  rw [TensorProduct.tmul_smul]
  exact congrArg (fun z : S.obj.obj U ↦ z ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)
    (mul_comm (α.hom.app U a) s)

section Coherence
variable {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (k : ∀ N P : Mod R, changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N))
    (hk : ∀ N P U s x y, ((k N P).hom.val.app U)
      (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y))

include hk

end Coherence

/-- scalarExtensionRawLift for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
-/
noncomputable def scalarExtensionRawLift
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H) :
    changeOfRingsPresheafOfUniverses α N ⟶ H.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (α.hom.app U).hom (f.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (α.hom.app V).hom (f.val.app V)
        (changeOfRingsMapOfUniverses α N i
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) = _
    rw [changeOfRingsMap_tmulOfUniverses, map_one]
    change (1 : S.obj.obj V) • (show H.val.obj V from f.val.app V (N.val.map i x)) =
      H.val.map i ((1 : S.obj.obj U) • (show H.val.obj U from f.val.app U x))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply f.val i x

/-- scalarExtensionLift for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
-/
noncomputable def scalarExtensionLift
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H) :
    changeOfRingsOfUniverses α N ⟶ H :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _).symm
      (scalarExtensionRawLift α N H f)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionLift_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionLift_tmul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (scalarExtensionLift α N H f).val.app U (scalarExtensionSection α N U s x) =
      s • (show H.val.obj U from f.val.app U x) := by
  have h := congrArg (fun g ↦ g.app U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x))
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _
        |>.apply_symm_apply (scalarExtensionRawLift α N H f))
  refine h.trans ?_
  rfl

namespace ScalarExtensionTensorCore

variable {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}

end ScalarExtensionTensorCore

end SheafOfModules
