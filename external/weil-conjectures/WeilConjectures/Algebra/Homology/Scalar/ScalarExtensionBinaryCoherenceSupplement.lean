/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
import Mathlib.Tactic.CategoryTheory.Slice
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence

/-!
# Binary scalar-extension comparisons

Source: Stacks Project, Tag 03EK.
(blueprint: lem-sp-scalar-extension-binary-coherence).
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

/-- The unit comparison is multiplication on scalar-extension pure sections.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: the sheafification adjunction sends the comparison back to sectionwise multiplication. -/
theorem scalarExtensionUnitIso_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U) :
    ((scalarExtensionUnitIso α).hom.val.app U) (scalarExtensionSection α (𝒪 R) U s a) =
      s * α.hom.app U a := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)
  have h : adj.homEquiv _ _ (scalarExtensionUnitIso α).hom = (scalarExtensionUnitRawIso α).hom := by
    change adj.homEquiv _ _
      (_ ≫ adj.counit.app (𝒪 S)) = _
    simp only [Functor.mapIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  have he := congrArg
    (fun f ↦ f.app U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] a)) h
  exact he.trans (by
    change (α.hom.app U a) * s = _
    exact mul_comm _ _)

/-- The unit comparison is the explicit multiplication construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def ScalarExtensionTensorCore.unitComparison
    {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}
    (_e : ScalarExtensionTensorCore R S α) :
    changeOfRingsOfUniverses α (𝒪 R) ≅ 𝒪 S := scalarExtensionUnitIso α

/-- scalarTensor_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensor_hom_ext {R : Sheaf J CommRingCat.{u}}
    (N P : Mod R) {H : Mod R} (f g : 𝒯 N P ⟶ H)
    (h : ∀ U x y, f.val.app U (siteSheafTensorTmul N P U x y) =
      g.val.app U (siteSheafTensorTmul N P U x y)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact h U x y

/-- scalarTensorTmul_naturality for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_naturality {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : N.val.obj U) (y : P.val.obj U) :
    (𝒯 N P).val.map i (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul N P V (N.val.map i x) (P.val.map i y) := by
  exact (PresheafOfModules.naturality_apply
    (scalarSheafificationUnit (siteTensorPresheaf N.val P.val)) i
      (x ⊗ₜ[R.obj.obj U] y)).symm

/-- scalarTensor_first_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensor_first_tmul {R : Sheaf J CommRingCat.{u}}
    {N N' : Mod R} (f : N ⟶ N') (P : Mod R) (U : Cᵒᵖ)
    (x : N.val.obj U) (y : P.val.obj U) :
    ((siteSheafTensorRight P).map f).val.app U (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul N' P U (f.val.app U x) y :=
  scalarSheafification_map_unit (siteTensorHom f.val P.val) U (x ⊗ₜ[R.obj.obj U] y)

/-- scalarTensor_second_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensor_second_tmul {R : Sheaf J CommRingCat.{u}}
    (N : Mod R) {P P' : Mod R} (g : P ⟶ P') (U : Cᵒᵖ)
    (x : N.val.obj U) (y : P.val.obj U) :
    (siteSheafTensorSecondMap N g).val.app U (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul N P' U x (g.val.app U y) :=
  scalarSheafification_map_unit (siteTensorSecondMap N.val g.val) U (x ⊗ₜ[R.obj.obj U] y)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_add for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_add
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x y : N.val.obj U) :
    scalarExtensionSection α N U s (x + y) =
      scalarExtensionSection α N U s x + scalarExtensionSection α N U s y := by
  dsimp only [scalarExtensionSection]
  rw [TensorProduct.tmul_add, map_add]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_zero for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_zero
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) :
    scalarExtensionSection α N U s 0 = 0 := by
  dsimp only [scalarExtensionSection]
  rw [TensorProduct.tmul_zero, map_zero]

/-- scalarExtension_tensor_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_tensor_hom_ext {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) {H : Mod S} (f g : changeOfRingsOfUniverses α (𝒯 N P) ⟶ H)
    (h : ∀ U s x y, f.val.app U
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      g.val.app U
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y))) :
    f = g := by
  apply scalarExtension_hom_ext α (𝒯 N P)
  intro U s z
  let η := scalarSheafificationUnit (siteTensorPresheaf N.val P.val)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (𝒯 N P).val.map i.op z at ht
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarExtensionSection_naturality, ← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | add t t' ih ih' =>
    simp only [map_add, scalarExtensionSection_add, ih, ih']
  | tmul x y => exact h (op V) (S.obj.map i.op s) x y

/-- scalarTensorTmul_add_first for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_add_first {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (x x' : N.val.obj U) (y : P.val.obj U) :
    siteSheafTensorTmul N P U (x + x') y =
      siteSheafTensorTmul N P U x y + siteSheafTensorTmul N P U x' y := by
  dsimp only [siteSheafTensorTmul]
  rw [TensorProduct.add_tmul, map_add]

/-- scalarTensorTmul_zero_first for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_zero_first {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (y : P.val.obj U) : siteSheafTensorTmul N P U 0 y = 0 := by
  dsimp only [siteSheafTensorTmul]
  rw [TensorProduct.zero_tmul, map_zero]

/-- scalarExtension_tensor3_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_tensor3_hom_ext {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P Q : Mod R) {H : Mod S} (f g : changeOfRingsOfUniverses α ((siteSheafTensorRight Q).obj
      ((siteSheafTensorRight P).obj N)) ⟶ H)
    (h : ∀ U s x y z, f.val.app U
        (scalarExtensionSection α ((siteSheafTensorRight Q).obj ((siteSheafTensorRight P).obj N))
          U s
          (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z)) =
      g.val.app U (scalarExtensionSection α ((siteSheafTensorRight Q).obj ((siteSheafTensorRight
        P).obj N)) U s
          (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z))) :
    f = g := by
  apply scalarExtension_tensor_hom_ext α (𝒯 N P) Q
  intro U s xy z
  let η := scalarSheafificationUnit (siteTensorPresheaf N.val P.val)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) xy)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (𝒯 N P).val.map i.op xy at ht
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarExtensionSection_naturality,
    scalarTensorTmul_naturality, ← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | add t t' ih ih' =>
    simp only [map_add, scalarTensorTmul_add_first, scalarExtensionSection_add, ih, ih']
  | tmul x y => exact h (op V) (S.obj.map i.op s) x y (Q.val.map i.op z)

section Coherence
variable {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (k : ∀ N P : Mod R, changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N))
    (hk : ∀ N P U s x y, ((k N P).hom.val.app U)
      (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y))

include hk

/-- scalarTensorComparison_associator for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_associator (N P Q : Mod R) :
    changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).associator N P Q).hom ≫
        (k N (𝒯 P Q)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N) (k P Q).hom =
      (k (𝒯 N P) Q).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α Q)).map (k N P).hom ≫
        ((scalarTensorCoherence S).associator (changeOfRingsOfUniverses α N)
          (changeOfRingsOfUniverses α P) (changeOfRingsOfUniverses α Q)).hom := by
  apply scalarExtension_tensor3_hom_ext α N P Q
  intro U s x y z
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtension_map_tmul, scalarTensorCoherence, scalarTensorAssociatorIso_tmul,
    hk, scalarTensor_first_tmul, scalarTensor_second_tmul]

/-- scalarTensorComparison_leftUnitor for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_leftUnitor (N : Mod R) :
    (k (𝒪 R) N).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map
          (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).leftUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).leftUnitor N).hom := by
  apply scalarExtension_tensor_hom_ext α (𝒪 R) N
  intro U s a x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hk,
    scalarTensor_first_tmul, scalarExtensionUnitIso_tmul, scalarTensorCoherence,
    scalarTensorLeftUnitor_tmul, scalarExtension_map_tmul]
  rw [scalarExtensionSection_base_smul, scalarExtensionSection_smul, mul_one]

/-- scalarTensorComparison_rightUnitor for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_rightUnitor (N : Mod R) :
    (k N (𝒪 R)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N)
          (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).rightUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).rightUnitor N).hom := by
  apply scalarExtension_tensor_hom_ext α N (𝒪 R)
  intro U s x a
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hk,
    scalarTensor_second_tmul, scalarExtensionUnitIso_tmul, scalarTensorCoherence,
    scalarTensorRightUnitor_tmul, scalarExtension_map_tmul, one_mul]
  rw [scalarExtensionSection_base_smul, scalarExtensionSection_smul, mul_comm]

/-- scalarTensorComparison_natural for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_natural {N N' P P' : Mod R} (f : N ⟶ N') (g : P ⟶ P') :
    changeOfRingsHomOfUniverses α _
        ((siteSheafTensorRight P).map f ≫ siteSheafTensorSecondMap N' g) ≫
        (k N' P').hom =
      (k N P).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α P)).map
          (changeOfRingsHomOfUniverses α N f) ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N')
          (changeOfRingsHomOfUniverses α P g) := by
  apply scalarExtension_tensor_hom_ext α N P
  intro U s x y
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtension_map_tmul, scalarTensor_first_tmul, scalarTensor_second_tmul, hk]
end Coherence

/-- scalarTensorBinaryInverseApp for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryInverseApp {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) :
    (siteTensorPresheaf (changeOfRingsPresheafOfUniverses α N)
      (changeOfRingsPresheafOfUniverses α P)).obj U ⟶
      (changeOfRingsPresheafOfUniverses α (𝒯 N P)).obj U := by
  letI := (α.hom.app U).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange
    (R.obj.obj U) (S.obj.obj U) (N.val.obj U) (P.val.obj U)).symm.toModuleIso.hom ≫
      (ModuleCat.extendScalars (α.hom.app U).hom).map
        ((scalarSheafificationUnit (siteTensorPresheaf N.val P.val)).app U)

/-- scalarTensorBinaryInverseApp_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryInverseApp_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (s t : S.obj.obj U)
    (x : N.val.obj U) (y : P.val.obj U) :
    scalarTensorBinaryInverseApp α N P U
      ((s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x) ⊗ₜ[S.obj.obj U]
        (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] y)) =
      (s * t) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] (siteSheafTensorTmul N P U x y) := by
  let := (α.hom.app U).hom.toAlgebra
  change (ModuleCat.extendScalars (α.hom.app U).hom).map
    ((scalarSheafificationUnit (siteTensorPresheaf N.val P.val)).app U)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange
      (R.obj.obj U) (S.obj.obj U) (N.val.obj U) (P.val.obj U)).symm
      ((s ⊗ₜ[R.obj.obj U] x) ⊗ₜ[S.obj.obj U] (t ⊗ₜ[R.obj.obj U] y))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
  rfl

/-- scalarTensorBinaryRawInverse for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryRawInverse {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    siteTensorPresheaf (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P) ⟶
      changeOfRingsPresheafOfUniverses α (𝒯 N P) where
  app U := scalarTensorBinaryInverseApp α N P U
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
    | tmul s x =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy']
      | tmul t y =>
        change scalarTensorBinaryInverseApp α N P V
          (changeOfRingsMapOfUniverses α N i (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)
            ⊗ₜ[S.obj.obj V] changeOfRingsMapOfUniverses α P i
              (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] y)) =
          changeOfRingsMapOfUniverses α (𝒯 N P) i
            (scalarTensorBinaryInverseApp α N P U
              ((s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x) ⊗ₜ[S.obj.obj U]
                (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] y)))
        rw [changeOfRingsMap_tmulOfUniverses, changeOfRingsMap_tmulOfUniverses,
          scalarTensorBinaryInverseApp_tmul, scalarTensorBinaryInverseApp_tmul,
          changeOfRingsMap_tmulOfUniverses, map_mul, scalarTensorTmul_naturality]

/-- scalarTensorBinaryDescentIso for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryDescentIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).obj
      (siteTensorPresheaf (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P)) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) :=
  scalarTensorSheafifyFirstIso (changeOfRingsPresheafOfUniverses α N)
      (changeOfRingsPresheafOfUniverses α P) ≪≫
    scalarTensorSheafifySecondIso (changeOfRingsPresheafOfUniverses α P)
      (changeOfRingsOfUniverses α N).val

/-- scalarTensorBinaryDescentIso_hom for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryDescentIso_hom {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ)
    (x : (changeOfRingsPresheafOfUniverses α N).obj U)
    (y : (changeOfRingsPresheafOfUniverses α P).obj U) :
    ((scalarTensorBinaryDescentIso α N P).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf
        (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P))).app U (x ⊗ₜ[S.obj.obj U] y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        ((scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)).app U x)
        ((scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α P)).app U y) := by
  change ((scalarTensorSheafifySecondIso (changeOfRingsPresheafOfUniverses α P)
      (changeOfRingsOfUniverses α N).val).hom.val.app U)
    (((scalarTensorSheafifyFirstIso (changeOfRingsPresheafOfUniverses α N)
      (changeOfRingsPresheafOfUniverses α P)).hom.val.app U) _) = _
  rw [scalarTensorSheafifyFirstIso_hom_tmul (R := S)]
  erw [scalarTensorSheafifySecondIso_hom_tmul (R := S)]
  rfl

/-- scalarTensorBinaryInverse for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryInverse {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) ⟶
      changeOfRingsOfUniverses α (𝒯 N P) :=
  (scalarTensorBinaryDescentIso α N P).inv ≫
    (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).map
        (scalarTensorBinaryRawInverse α N P)

/-- scalarTensorBinaryInverse_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryInverse_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (s t : S.obj.obj U)
    (x : N.val.obj U) (y : P.val.obj U) :
    (scalarTensorBinaryInverse α N P).val.app U
      (siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U t y)) =
      scalarExtensionSection α (𝒯 N P) U (s * t) (siteSheafTensorTmul N P U x y) := by
  let := (α.hom.app U).hom.toAlgebra
  let z := (scalarSheafificationUnit (siteTensorPresheaf
    (changeOfRingsPresheafOfUniverses α N) (changeOfRingsPresheafOfUniverses α P))).app U
      ((s ⊗ₜ[R.obj.obj U] x) ⊗ₜ[S.obj.obj U] (t ⊗ₜ[R.obj.obj U] y))
  have he := scalarTensorBinaryDescentIso_hom α N P U
    (s ⊗ₜ[R.obj.obj U] x) (t ⊗ₜ[R.obj.obj U] y)
  change ((scalarTensorBinaryDescentIso α N P).hom.val.app U) z =
    siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
      (scalarExtensionSection α N U s x) (scalarExtensionSection α P U t y) at he
  rw [← he]
  unfold scalarTensorBinaryInverse
  change (((scalarTensorBinaryDescentIso α N P).hom ≫
    (scalarTensorBinaryDescentIso α N P).inv ≫
    (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).map
        (scalarTensorBinaryRawInverse α N P)).val.app U) z = _
  rw [Iso.hom_inv_id_assoc]
  dsimp only [z]
  rw [scalarSheafification_map_unit]
  exact congrArg ((scalarSheafificationUnit
    (changeOfRingsPresheafOfUniverses α (𝒯 N P))).app U)
      (scalarTensorBinaryInverseApp_tmul α N P U s t x y)

/-- scalarTensorTmul_smul_first for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_smul_first {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U) (y : P.val.obj U) :
    siteSheafTensorTmul N P U (a • x) y = a • siteSheafTensorTmul N P U x y := by
  dsimp only [siteSheafTensorTmul]
  rw [← TensorProduct.smul_tmul', map_smul]

/-- scalarTensorTmul_smul_second for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_smul_second {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U) (y : P.val.obj U) :
    siteSheafTensorTmul N P U x (a • y) = a • siteSheafTensorTmul N P U x y := by
  dsimp only [siteSheafTensorTmul]
  erw [TensorProduct.tmul_smul, map_smul]

/-- scalarTensorBinaryPair for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryPair {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) :
    N.val.obj U →ₗ[R.obj.obj U] P.val.obj U →ₗ[R.obj.obj U]
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
          N))).val.obj U) := by
  let H := ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
    N))
  let : Module (R.obj.obj U) (H.val.obj U) :=
    Module.compHom (H.val.obj U) (α.hom.app U).hom
  apply LinearMap.mk₂ (R.obj.obj U)
    (fun x y ↦ siteSheafTensorTmul (changeOfRingsOfUniverses α N)
      (changeOfRingsOfUniverses α P) U
      (scalarExtensionSection α N U 1 x) (scalarExtensionSection α P U 1 y))
  · intro x x' y
    dsimp only [siteSheafTensorTmul]
    rw [scalarExtensionSection_add, TensorProduct.add_tmul, map_add]
  · intro a x y
    change siteSheafTensorTmul _ _ U (scalarExtensionSection α N U 1 (a • x)) _ =
      α.hom.app U a • siteSheafTensorTmul _ _ U _ _
    rw [scalarExtensionSection_base_smul, one_mul,
      ← scalarTensorTmul_smul_first, scalarExtensionSection_smul, mul_one]
  · intro x y y'
    dsimp only [siteSheafTensorTmul]
    rw [scalarExtensionSection_add, TensorProduct.tmul_add, map_add]
  · intro a x y
    change siteSheafTensorTmul _ _ U _ (scalarExtensionSection α P U 1 (a • y)) =
      α.hom.app U a • siteSheafTensorTmul _ _ U _ _
    rw [scalarExtensionSection_base_smul, one_mul,
      ← scalarTensorTmul_smul_second, scalarExtensionSection_smul, mul_one]

/-- scalarTensorBinaryRawForward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryRawForward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    siteTensorPresheaf N.val P.val ⟶
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
          N))).val) where
  app U := ModuleCat.ofHom (Y :=
    (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
        N))).val.obj U))
    (TensorProduct.lift (scalarTensorBinaryPair α N P U))
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change siteSheafTensorTmul _ _ V
      (scalarExtensionSection α N V 1 (N.val.map i x))
      (scalarExtensionSection α P V 1 (P.val.map i y)) =
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
          N)).val.map i
          (siteSheafTensorTmul _ _ U (scalarExtensionSection α N U 1 x)
            (scalarExtensionSection α P U 1 y))
    rw [scalarTensorTmul_naturality, scalarExtensionSection_naturality,
      scalarExtensionSection_naturality, map_one]

/-- scalarTensorBinaryBaseForward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryBaseForward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    𝒯 N P ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N)) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).homEquiv _ _).symm
      (scalarTensorBinaryRawForward α N P)

/-- scalarTensorBinaryBaseForward_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryBaseForward_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (x : N.val.obj U) (y : P.val.obj U) :
    (scalarTensorBinaryBaseForward α N P).val.app U (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U 1 x) (scalarExtensionSection α P U 1 y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h : adj.homEquiv (siteTensorPresheaf N.val P.val)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N)))
      (scalarTensorBinaryBaseForward α N P) = scalarTensorBinaryRawForward α N P :=
    Equiv.apply_symm_apply _ _
  exact congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] y)) h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarTensorBinaryForward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryForward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    changeOfRingsOfUniverses α (𝒯 N P) ⟶
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) :=
  scalarExtensionLift α (𝒯 N P) _ (scalarTensorBinaryBaseForward α N P)

/-- scalarTensorBinaryForward_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryForward_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) (y : P.val.obj U) :
    (scalarTensorBinaryForward α N P).val.app U
      (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y) := by
  rw [scalarTensorBinaryForward, scalarExtensionLift_tmul, scalarTensorBinaryBaseForward_tmul]
  rw [← scalarTensorTmul_smul_first, scalarExtensionSection_smul, mul_one]

/-- scalarTensorBinaryForward_inverse for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryForward_inverse {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    scalarTensorBinaryForward α N P ≫ scalarTensorBinaryInverse α N P = 𝟙 _ := by
  apply scalarExtension_tensor_hom_ext α N P
  intro U s x y
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarTensorBinaryForward_tmul, scalarTensorBinaryInverse_tmul, mul_one,
    id_val, PresheafOfModules.id_app, ModuleCat.id_apply]

/-- scalarTensorBinaryInverse_forward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryInverse_forward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    scalarTensorBinaryInverse α N P ≫ scalarTensorBinaryForward α N P = 𝟙 _ := by
  apply (cancel_epi (scalarTensorBinaryDescentIso α N P).hom).1
  simp only [Category.comp_id]
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _
      |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z w
  change (scalarTensorBinaryForward α N P).val.app U
    ((scalarTensorBinaryInverse α N P).val.app U
      (((scalarTensorBinaryDescentIso α N P).hom.val.app U)
        ((scalarSheafificationUnit (siteTensorPresheaf
          (changeOfRingsPresheafOfUniverses α N)
          (changeOfRingsPresheafOfUniverses α P))).app U (z ⊗ₜ[S.obj.obj U] w)))) =
    ((scalarTensorBinaryDescentIso α N P).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf
        (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P))).app U (z ⊗ₜ[S.obj.obj U] w))
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [TensorProduct.add_tmul, map_add, hz, hz']
  | tmul s x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | tmul t y =>
      change S.obj.obj U at s t
      rw [scalarTensorBinaryDescentIso_hom]
      change (scalarTensorBinaryForward α N P).val.app U
        ((scalarTensorBinaryInverse α N P).val.app U
          (siteSheafTensorTmul _ _ U (scalarExtensionSection α N U s x)
            (scalarExtensionSection α P U t y))) = _
      rw [scalarTensorBinaryInverse_tmul, scalarTensorBinaryForward_tmul]
      change siteSheafTensorTmul _ _ U (scalarExtensionSection α N U (s * t) x)
        (scalarExtensionSection α P U 1 y) =
          siteSheafTensorTmul _ _ U (scalarExtensionSection α N U s x)
            (scalarExtensionSection α P U t y)
      rw [mul_comm s t, ← scalarExtensionSection_smul α N U t s,
        scalarTensorTmul_smul_first]
      have ht := scalarExtensionSection_smul α P U t 1 y
      rw [mul_one] at ht
      rw [← ht, scalarTensorTmul_smul_second]

/-- scalarTensorBinaryIso for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) where
  hom := scalarTensorBinaryForward α N P
  inv := scalarTensorBinaryInverse α N P
  hom_inv_id := scalarTensorBinaryForward_inverse α N P
  inv_hom_id := scalarTensorBinaryInverse_forward α N P

/-- Existence of normalized binary scalar-extension comparisons.
Source: Stacks Project, Tag 03EK, tensor-product formulas
(blueprint: lem-sp-scalar-extension-binary-coherence).

Proof: construct the sectionwise associator and the two unitors from the tensor
universal property, and descend through module sheafification. Their inverses send
`x ⊗ (y ⊗ z)` to `(x ⊗ y) ⊗ z`, and send `x` to `1 ⊗ x` or `x ⊗ 1`.
For extension of scalars the unit comparison is `s ⊗ a ↦ s α(a)`, with inverse
`s ↦ s ⊗ 1`. The binary comparison sends `s ⊗ (x ⊗ y)` to
`(s ⊗ x) ⊗ (1 ⊗ y)`. Its inverse sends `(s ⊗ x) ⊗ (t ⊗ y)` to
`st ⊗ (x ⊗ y)`. Balancing makes these linear maps; tensor descent through
sheafification extends them to the sheaf tensors, and their composites are identity
on pure inputs, hence identity by the sheafification universal property.
The associator square, both unitor squares, and the bifunctor naturality square
commute on pure inputs: their values use the same restricted sections and products
of scalars. Repeated tensor descent therefore proves all the required equalities.
No tensor powers, duals, flatness or rank assumptions enter this construction. -/
theorem exists_scalarExtensionTensorCore
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) :
    Nonempty (ScalarExtensionTensorCore R S α) := by
  let k := scalarTensorBinaryIso α
  have hk := scalarTensorBinaryForward_tmul α
  exact ⟨{
    tensorComparison := k
    tensor_tmul := hk
    associator_compat := scalarTensorComparison_associator α k hk
    leftUnitor_compat := scalarTensorComparison_leftUnitor α k hk
    rightUnitor_compat := scalarTensorComparison_rightUnitor α k hk
    tensor_natural := scalarTensorComparison_natural α k hk }⟩

/-- Scalar extension preserves identity morphisms.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: extension of scalars preserves identities sectionwise, and so does sheafification. -/
theorem scalarExtension_map_id {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) : changeOfRingsHomOfUniverses α N (𝟙 N) = 𝟙 _ := by
  let a := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
  let t : changeOfRingsPresheafOfUniverses α N ⟶ changeOfRingsPresheafOfUniverses α N :=
    { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (𝟙 (N.val.obj U))
      naturality := changeOfRingsHom_naturalityOfUniverses α N (𝟙 N) }
  have ht : t = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id (N.val.obj U)
  change a.map t = 𝟙 _
  rw [ht]
  exact a.map_id _

/-- Scalar extension preserves composites of module morphisms.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: both extension of scalars on sections and module sheafification are functors. -/
theorem scalarExtension_map_comp {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    {N P Q : Mod R} (f : N ⟶ P) (g : P ⟶ Q) :
    changeOfRingsHomOfUniverses α N (f ≫ g) =
      changeOfRingsHomOfUniverses α N f ≫ changeOfRingsHomOfUniverses α P g := by
  unfold changeOfRingsHomOfUniverses
  rw [← Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp (f.val.app U) (g.val.app U)

/-- An identity in the second tensor factor induces the identity.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: `id ⊗ id` is the identity sectionwise; sheafification preserves identities. -/
theorem scalarTensor_second_id {R : Sheaf J CommRingCat.{u}} (N P : Mod R) :
    siteSheafTensorSecondMap N (𝟙 P) = 𝟙 (𝒯 N P) := by
  let a := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let t : siteTensorPresheaf N.val P.val ⟶ siteTensorPresheaf N.val P.val :=
    siteTensorSecondMap N.val (𝟙 P.val)
  have ht : t = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  change a.map t = 𝟙 _
  rw [ht]
  exact a.map_id _

namespace ScalarExtensionTensorCore

variable {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}

/-- Binary comparison naturality with the right factor fixed.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: specialize bifunctor naturality to an identity in the second factor. -/
theorem first_natural (e : ScalarExtensionTensorCore R S α)
    {N N' : Mod R} (f : N ⟶ N') (P : Mod R) :
    changeOfRingsHomOfUniverses α _ ((siteSheafTensorRight P).map f) ≫
        (e.tensorComparison N' P).hom =
      (e.tensorComparison N P).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α P)).map
          (changeOfRingsHomOfUniverses α N f) := by
  simpa only [scalarTensor_second_id, Category.comp_id, scalarExtension_map_id] using
    e.tensor_natural f (𝟙 P)

/-- Construct power comparisons recursively from the binary comparison.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def power (e : ScalarExtensionTensorCore R S α) (N : Mod R) :
    ∀ r : ℕ, changeOfRingsOfUniverses α (scalarTensorPower R N r) ≅
      scalarTensorPower S (changeOfRingsOfUniverses α N) r
  | 0 => e.unitComparison
  | 1 => Iso.refl _
  | r + 2 => e.tensorComparison (scalarTensorPower R N (r + 1)) N ≪≫
      (siteSheafTensorRight (changeOfRingsOfUniverses α N)).mapIso (e.power N (r + 1))

end ScalarExtensionTensorCore

end SheafOfModules
