/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerInjectiveComponents
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerEvaluationAdjoint
import Mathlib.CategoryTheory.Monad.Adjunction

set_option linter.privateModule false

/-! # Ordinary coefficient-tower inverse-image ingredients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {T S : Scheme.{t}} (g : T ⟶ S)

private def restrictionIdentity (X : Scheme.{t}) (n : ℕ) :
    systemRestriction (spCoefficientCommRings l E X) (Nat.le_refl n) ≅ 𝟭 _ := by
  let B := spCoefficientCommRings l E X
  have hid (U : X.ProEtᵒᵖ) :
      (((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat RingCat)).map
        (B.map (homOfLE (Nat.le_refl n)).op)).hom.app U).hom = RingHom.id _ := by
    have h := (B ⋙ sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat RingCat)).map_id (op n)
    exact congrArg (fun f ↦ (f.hom.app U).hom) h
  exact NatIso.ofComponents (fun J ↦
    { hom := { val :=
        { app := fun U ↦ (ModuleCat.restrictScalarsId'App _ (hid U) (J.val.obj U)).hom
          naturality := fun f ↦ by ext x; rfl } }
      inv := { val :=
        { app := fun U ↦ (ModuleCat.restrictScalarsId'App _ (hid U) (J.val.obj U)).inv
          naturality := fun f ↦ by ext x; rfl } }
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (by intros; ext U x; rfl)

private theorem bijective_heq.{v} {A B A' B' : Type v}
    (hA : A = A') (hB : B = B') {f : A → B} {f' : A' → B'}
    (h : HEq f f') : Function.Bijective f ↔ Function.Bijective f' := by
  subst A'
  subst B'
  cases h
  rfl

section Generic
universe a v w
variable {C : Type a} [Category.{v} C] {K : GrothendieckTopology C}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (B : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})

variable [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]

end Generic

section GenericIso
universe a v w
variable {C : Type a} [Category.{v} C] {K : GrothendieckTopology C}

variable [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})

end GenericIso

private theorem moduleHom_bijective_heq.{v, w} {R : Type w} [Ring R]
    {M M' N N' : ModuleCat.{v} R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {f' : M' ⟶ N'} (h : HEq f f') :
    Function.Bijective (fun x ↦ f x) ↔ Function.Bijective (fun x ↦ f' x) := by
  subst M'
  subst N'
  cases h
  rfl

end AlgebraicGeometry.ProEtale
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
