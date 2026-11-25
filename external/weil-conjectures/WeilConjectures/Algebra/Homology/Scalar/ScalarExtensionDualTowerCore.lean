/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso

/-!
# Duals and binary ring towers under scalar extension

Source: Stacks Project, Tags 03EK, 03EM, 04TT.
(blueprint: lem-sp-scalar-extension-dual-tower-core).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
-- Universe-polymorphic sheafification instances make the section-variable linter expensive.
set_option linter.unusedSectionVars false

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

attribute [local irreducible] scalarExtensionLift
  scalarExtensionDualMap scalarExtensionUnitIso changeOfRingsHomOfUniverses

section Universes

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
  [HasWeakSheafify J AddCommGrpCat.{max u m}]

/-- scalarExtensionEmbedding: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionEmbedding {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      (changeOfRingsOfUniverses α N) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (Y :=
        (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
          (changeOfRingsOfUniverses α N)).val.obj U))
        { toFun := fun x ↦ scalarExtensionSection α N U 1 x
          map_add' := scalarExtensionSection_add α N U 1
          map_smul' := by
            intro a x
            change scalarExtensionSection α N U 1 (a • x) =
              α.hom.app U a • scalarExtensionSection α N U 1 x
            erw [scalarExtensionSection_base_smul, one_mul,
              scalarExtensionSection_smul, mul_one] }
      naturality := by
        intro U V i
        ext x
        change scalarExtensionSection α N V 1 (N.val.map i x) =
          (changeOfRingsOfUniverses α N).val.map i (scalarExtensionSection α N U 1 x)
        erw [scalarExtensionSection_naturality, map_one] }

/-- scalarExtensionTowerMiddle: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerMiddle {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses α N ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map β)).obj
        (changeOfRingsOfUniverses (α ≫ β) N) :=
  scalarExtensionLift α N _
    { val :=
        { app := fun U ↦ ModuleCat.ofHom (Y :=
            (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
              ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map β)).obj
                (changeOfRingsOfUniverses (α ≫ β) N))).val.obj U))
            { toFun := fun x ↦ scalarExtensionSection (α ≫ β) N U 1 x
              map_add' := scalarExtensionSection_add (α ≫ β) N U 1
              map_smul' := by
                intro a x
                change scalarExtensionSection (α ≫ β) N U 1 (a • x) =
                  β.hom.app U (α.hom.app U a) •
                    scalarExtensionSection (α ≫ β) N U 1 x
                erw [scalarExtensionSection_base_smul, one_mul,
                  scalarExtensionSection_smul, mul_one]
                rfl }
          naturality := by
            intro U V i
            ext x
            change scalarExtensionSection (α ≫ β) N V 1 (N.val.map i x) =
              (changeOfRingsOfUniverses (α ≫ β) N).val.map i
                (scalarExtensionSection (α ≫ β) N U 1 x)
            erw [scalarExtensionSection_naturality, map_one] } }

/-- scalarExtensionTowerForward: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerForward {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ⟶
      changeOfRingsOfUniverses (α ≫ β) N :=
  scalarExtensionLift β (changeOfRingsOfUniverses α N) _
    (scalarExtensionTowerMiddle α β N)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTowerForward_tmul: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTowerForward_tmul {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (a : T.obj.obj U) (s : S.obj.obj U) (x : N.val.obj U) :
    (scalarExtensionTowerForward α β N).val.app U
      (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U s x)) =
      scalarExtensionSection (α ≫ β) N U (a * β.hom.app U s) x := by
  rw [scalarExtensionTowerForward, scalarExtensionLift_tmul]
  unfold scalarExtensionTowerMiddle
  rw [scalarExtensionLift_tmul]
  change a • (β.hom.app U s • scalarExtensionSection (α ≫ β) N U 1 x) = _
  rw [scalarExtensionSection_smul, mul_one, scalarExtensionSection_smul]

/-- scalarExtensionTowerBaseReverse: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerBaseReverse {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map (α ≫ β))).obj
      (changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N)) :=
  scalarExtensionEmbedding α N ≫
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).map
      (scalarExtensionEmbedding β (changeOfRingsOfUniverses α N))

/-- scalarExtensionTowerReverse: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerReverse {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses (α ≫ β) N ⟶
      changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) :=
  scalarExtensionLift (α ≫ β) N _ (scalarExtensionTowerBaseReverse α β N)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTowerReverse_tmul: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTowerReverse_tmul {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (a : T.obj.obj U) (x : N.val.obj U) :
    (scalarExtensionTowerReverse α β N).val.app U
      (scalarExtensionSection (α ≫ β) N U a x) =
      scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U 1 x) := by
  rw [scalarExtensionTowerReverse, scalarExtensionLift_tmul]
  unfold scalarExtensionTowerBaseReverse scalarExtensionEmbedding
  change a • scalarExtensionSection β (changeOfRingsOfUniverses α N) U 1
    (scalarExtensionSection α N U 1 x) = _
  rw [scalarExtensionSection_smul, mul_one]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTower_hom_ext: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTower_hom_ext {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) {H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj T)}
    (f g : changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ⟶ H)
    (h : ∀ U a s x, f.val.app U
      (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U s x)) =
      g.val.app U (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U s x))) : f = g := by
  apply scalarExtension_hom_ext β (changeOfRingsOfUniverses α N)
  intro U a z
  let η := scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (changeOfRingsOfUniverses α N).val.map i.op z at ht
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarExtensionSection_naturality, ← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | add t t' ih ih' =>
    erw [(η.app (op V)).hom.map_add, scalarExtensionSection_add,
      (f.val.app (op V)).hom.map_add, (g.val.app (op V)).hom.map_add, ih, ih']
  | tmul s x =>
    simpa only [η, scalarSheafificationUnit, scalarExtensionSection] using!
      h (op V) (T.obj.map i.op a) s x

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTower_reverse_forward: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTower_reverse_forward {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    scalarExtensionTowerReverse α β N ≫ scalarExtensionTowerForward α β N = 𝟙 _ := by
  apply scalarExtension_hom_ext (α ≫ β) N
  intro U a x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtensionTowerReverse_tmul, scalarExtensionTowerForward_tmul, map_one, mul_one,
    id_val, PresheafOfModules.id_app, ModuleCat.id_apply]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTower_forward_reverse: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTower_forward_reverse {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    scalarExtensionTowerForward α β N ≫ scalarExtensionTowerReverse α β N = 𝟙 _ := by
  apply scalarExtensionTower_hom_ext α β N
  intro U a s x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtensionTowerForward_tmul, scalarExtensionTowerReverse_tmul,
    id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  have hs := scalarExtensionSection_smul α N U s 1 x
  rw [mul_one] at hs
  rw [← hs, scalarExtensionSection_base_smul]

/-- scalarExtensionTowerIso: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerIso {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ≅
      changeOfRingsOfUniverses (α ≫ β) N where
  hom := scalarExtensionTowerForward α β N
  inv := scalarExtensionTowerReverse α β N
  hom_inv_id := scalarExtensionTower_forward_reverse α β N
  inv_hom_id := scalarExtensionTower_reverse_forward α β N

/-- The tower comparison has the explicitly constructed forward component.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-dual-tower-core). -/
theorem scalarExtensionTowerIso_hom {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarExtensionTowerIso α β N).hom = scalarExtensionTowerForward α β N := rfl

attribute [irreducible] scalarExtensionTowerIso

end Universes

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] changeOfRingsOfUniverses scalarExtensionSection
  siteSheafTensorTmul siteSheafTensorRight siteSheafTensorSecondMap


attribute [local irreducible] scalarExtensionTowerForward scalarExtensionTowerReverse

end SheafOfModules
