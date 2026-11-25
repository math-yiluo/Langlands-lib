/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Tensor powers and duals under scalar extension

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-scalar-extension/
  sk-def-sp-scalar-extension-functor.proof.md, proof paragraphs (3) and (4),
  tensor powers and dual evaluation under ordinary scalar extension
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe uC vC u m

open CategoryTheory CategoryTheory.Limits
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

/-- The image of a pure scalar-extension tensor under the module sheafification unit.
The module universe may exceed the coefficient universe, as happens for internal Hom.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
noncomputable def scalarExtensionSection
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsOfUniverses α M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses α M)).app U)
        (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection
  siteSheafTensorTmul siteSheafTensorRight siteSheafTensorSecondMap

/-- Canonical associators and unitors for the actual sheafified tensor product.
Each isomorphism is specified by its action on local pure tensors, rather than an
unspecified monoidal structure. Source: Stacks, Tag 03EK
(auxiliary; not a blueprint node). -/
structure ScalarTensorCoherence (R : Sheaf J CommRingCat.{u}) where
  associator : ∀ (N P Q : Mod R), 𝒯 (𝒯 N P) Q ≅ 𝒯 N (𝒯 P Q)
  associator_tmul : ∀ (N P Q : Mod R) (U : Cᵒᵖ)
      (x : N.val.obj U) (y : P.val.obj U) (z : Q.val.obj U),
    ((associator N P Q).hom.val.app U)
        (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z) =
      siteSheafTensorTmul N (𝒯 P Q) U x (siteSheafTensorTmul P Q U y z)
  leftUnitor : ∀ N : Mod R, 𝒯 (𝒪 R) N ≅ N
  leftUnitor_tmul : ∀ (N : Mod R) (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U),
    ((leftUnitor N).hom.val.app U) (siteSheafTensorTmul (𝒪 R) N U a x) = a • x
  rightUnitor : ∀ N : Mod R, 𝒯 N (𝒪 R) ≅ N
  rightUnitor_tmul : ∀ (N : Mod R) (U : Cᵒᵖ) (x : N.val.obj U) (a : R.obj.obj U),
    ((rightUnitor N).hom.val.app U) (siteSheafTensorTmul N (𝒪 R) U x a) = a • x

end SheafOfModules
