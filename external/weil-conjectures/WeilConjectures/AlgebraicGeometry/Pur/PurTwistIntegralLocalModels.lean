/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientTensor
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Integral and finite local models of the scalar-extended root line

## References

* Stacks Project, Tags 03EK, 03PK and 03RV
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

-- Sectionwise tensor cancellation for the coefficient pushout.
private noncomputable def pushoutModuleEquiv
    {A B R T M : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing T]
    [AddCommGroup M] [Module R M] (a : A →+* R) (b : A →+* B)
    (c : R →+* T) (d : B →+* T) (_hsq : d.comp b = c.comp a)
    (q : letI := b.toAlgebra; letI := a.toAlgebra; B ⊗[A] R ≃+* T)
    (hq : ∀ s r, letI := b.toAlgebra; letI := a.toAlgebra;
      q (s ⊗ₜ[A] r) = d s * c r) :
    letI := b.toAlgebra
    letI := a.toAlgebra
    letI := c.toAlgebra
    letI := Module.compHom M a
    (B ⊗[A] M) ≃+ (T ⊗[R] M) := by
  letI := b.toAlgebra
  letI := a.toAlgebra
  letI := c.toAlgebra
  letI := Module.compHom M a
  let : IsScalarTower A R M := ⟨fun x y z ↦ mul_smul (a x) y z⟩
  let : SMulCommClass R A M := ⟨fun x y z ↦ by
    change x • a y • z = a y • x • z
    rw [← mul_smul, mul_comm, mul_smul]⟩
  let e : R ⊗[A] B ≃ₐ[R] T :=
    { __ := (Algebra.TensorProduct.comm A R B).toRingEquiv.trans q
      commutes' := by
        intro r
        change q (1 ⊗ₜ[A] r) = c r
        rw [hq, map_one, one_mul] }
  exact (((TensorProduct.AlgebraTensorModule.cancelBaseChange A R R M B).symm.trans
    (TensorProduct.comm R M (R ⊗[A] B))).restrictScalars A).toAddEquiv.symm.trans
    (TensorProduct.comm A B M).toAddEquiv.symm |>.symm.trans
      (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)).toAddEquiv
private theorem pushoutModuleEquiv_tmul
    {A B R T M : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing T]
    [AddCommGroup M] [Module R M] (a : A →+* R) (b : A →+* B)
    (c : R →+* T) (d : B →+* T) (hsq : d.comp b = c.comp a)
    (q : letI := b.toAlgebra; letI := a.toAlgebra; B ⊗[A] R ≃+* T)
    (hq : ∀ s r, letI := b.toAlgebra; letI := a.toAlgebra;
      q (s ⊗ₜ[A] r) = d s * c r) (s : B) (x : M) :
    letI := b.toAlgebra
    letI := a.toAlgebra
    letI := c.toAlgebra
    letI := Module.compHom M a
    pushoutModuleEquiv a b c d hsq q hq (s ⊗ₜ[A] x) = d s ⊗ₜ[R] x := by
  dsimp [pushoutModuleEquiv]
  rw [hq, map_one, mul_one]

-- The prescribed completed action restricts to the original discrete action.
private noncomputable def integralForgetIso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistIntegralCompletionMap S l E))).obj (purTwistIntegralModule S l E) ≅
      purTwistIntegralOne S l E := by
  let hd := (purTwistIntegralAction_existsUnique S l E).exists.choose_spec.2.1
  let f : (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistIntegralCompletionMap S l E))).obj (purTwistIntegralModule S l E) ⟶
      purTwistIntegralOne S l E :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistIntegralCompletionMap S l E))).obj
                (purTwistIntegralModule S l E)).val.obj U)
        (Y := (purTwistIntegralOne S l E).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ hd U a x }
       naturality := by intros; ext; rfl }⟩
  let g : purTwistIntegralOne S l E ⟶ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistIntegralCompletionMap S l E))).obj (purTwistIntegralModule S l E) :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (purTwistIntegralOne S l E).val.obj U)
        (Y := ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistIntegralCompletionMap S l E))).obj
                (purTwistIntegralModule S l E)).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ (hd U a x).symm }
       naturality := by intros; ext; rfl }⟩
  exact ⟨f, g, by ext; rfl, by ext; rfl⟩

private theorem integralForgetIso_hom_apply
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) (x : (purTwistIntegralModule S l E).val.obj U) :
    (integralForgetIso S l E).hom.val.app U x = x := rfl

attribute [local irreducible] integralForgetIso

private noncomputable def rootToIntegral
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    purTwistZlModule S l ⟶ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistCompletedScalarMap S l E))).obj (purTwistIntegralModule S l E) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (purTwistZlModule S l).val.obj U)
        (Y := ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistCompletedScalarMap S l E))).obj
                (purTwistIntegralModule S l E)).val.obj U)
        { toFun := fun x ↦ purTwistIntegralTensor S l E U 1 x
          map_add' := by
            intro x y
            unfold purTwistIntegralTensor
            rw [TensorProduct.tmul_add, map_add]
          map_smul' := by
            intro a x
            exact ((purTwistIntegralAction_existsUnique S l E).exists.choose_spec.2.2
              U a 1 x).symm }
      naturality := by
        intro U V f
        ext x
        have h := SheafOfModules.scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
          (purTwistConstantIntegersMap S l E)
          ((SheafOfModules.restrictScalars.{u + 1}
            ((sheafCompose (ProEt.topology S)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)) f 1 x
        change purTwistIntegralTensor S l E V 1 ((purTwistZlModule S l).val.map f x) =
          (purTwistIntegralOne S l E).val.map f (purTwistIntegralTensor S l E U 1 x)
        rw [map_one] at h
        exact h.symm }

private noncomputable def integralExtensionReverse
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} (purTwistCompletedScalarMap S l E)
    (purTwistZlModule S l) (purTwistIntegralModule S l E) (rootToIntegral S l E)

private theorem integralExtensionReverse_section
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ)
    (a : (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    (integralExtensionReverse S l E).val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (purTwistCompletedScalarMap S l E) (purTwistZlModule S l) U a x) =
    @SMul.smul _ _ (purTwistIntegralAction S l E U).toSMul a
      (purTwistIntegralTensor S l E U 1 x) := by
  exact SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}
    (purTwistCompletedScalarMap S l E) (purTwistZlModule S l)
    (purTwistIntegralModule S l E) (rootToIntegral S l E) U a x

attribute [local irreducible] integralExtensionReverse

private noncomputable def restrictionSheafificationComparison
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {R B : Sheaf J RingCat.{u + 1}} (α : R ⟶ B)
    (P : _root_.PresheafOfModules.{u + 1} B.obj) :
    (_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((_root_.PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (SheafOfModules.restrictScalars α).obj
          ((_root_.PresheafOfModules.sheafification (𝟙 B.obj)).obj P) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    ((_root_.PresheafOfModules.restrictScalars α.hom).map
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P))

private theorem restrictionSheafificationComparison_isIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {R B : Sheaf J RingCat.{u + 1}} (α : R ⟶ B)
    (P : _root_.PresheafOfModules.{u + 1} B.obj) :
    IsIso (restrictionSheafificationComparison α P) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)]
  have he : (SheafOfModules.toSheaf R).map
      (restrictionSheafificationComparison α P) = 𝟙 _ := by
    unfold restrictionSheafificationComparison
    rw [_root_.PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{u + 1}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (_root_.PresheafOfModules.toPresheaf B.obj).map
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact _root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance

private theorem restrictionSheafificationComparison_unit
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {R B : Sheaf J RingCat.{u + 1}} (α : R ⟶ B)
    (P : _root_.PresheafOfModules.{u + 1} B.obj) (U : Cᵒᵖ) (x : P.obj U) :
    (restrictionSheafificationComparison α P).val.app U
        (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
          ((_root_.PresheafOfModules.restrictScalars α.hom).obj P)).app U x) =
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P).app U x := by
  exact congrArg (fun k ↦ k.app U x)
    ((_root_.PresheafOfModules.sheafificationHomEquiv
      (P := (_root_.PresheafOfModules.restrictScalars α.hom).obj P)
      (F := (SheafOfModules.restrictScalars α).obj
        ((_root_.PresheafOfModules.sheafification (𝟙 B.obj)).obj P))
      (𝟙 R.obj)).apply_symm_apply
      ((_root_.PresheafOfModules.restrictScalars α.hom).map
        ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P)))

private theorem sheafification_map_unit
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    (R : Sheaf J RingCat.{u + 1}) {P Q : _root_.PresheafOfModules.{u + 1} R.obj}
    (f : P ⟶ Q) (U : Cᵒᵖ) (x : P.obj U) :
    ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).map f).val.app U
      (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P).app U x) =
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q).app U
      (f.app U x) := by
  exact (congrArg (fun k ↦ k.app U x)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality f)).symm

private theorem sheafification_restrict_map_unit
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {R B : Sheaf J RingCat.{u + 1}} (α : R ⟶ B)
    {P : _root_.PresheafOfModules.{u + 1} B.obj}
    {Q : _root_.PresheafOfModules.{u + 1} R.obj}
    (f : Q ⟶ (_root_.PresheafOfModules.restrictScalars α.hom).obj P)
    (U : Cᵒᵖ) (x : Q.obj U) :
    (((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).map f ≫
        restrictionSheafificationComparison α P).val.app U)
      (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q).app U x) =
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P).app U
      (f.app U x) := by
  simp only [SheafOfModules.comp_val, _root_.PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [sheafification_map_unit, restrictionSheafificationComparison_unit]

attribute [local irreducible] restrictionSheafificationComparison

private noncomputable def integralRawForwardApp
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (U : S.ProEtᵒᵖ) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistConstantIntegersMap S l E)
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l))).obj U ⟶
      ((_root_.PresheafOfModules.restrictScalars
        (Functor.whiskerRight (purTwistIntegralCompletionMap S l E).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj
        (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistCompletedScalarMap S l E) (purTwistZlModule S l))).obj U :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    ((purTwistConstantIntegersMap S l E).hom.app U).hom
    (Y := ((_root_.PresheafOfModules.restrictScalars
      (Functor.whiskerRight (purTwistIntegralCompletionMap S l E).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj
            (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
              (purTwistCompletedScalarMap S l E) (purTwistZlModule S l))).obj U)
    (ModuleCat.ofHom
      (X := ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)).val.obj U)
      (Y := (ModuleCat.restrictScalars
        ((purTwistConstantIntegersMap S l E).hom.app U).hom).obj
          (((_root_.PresheafOfModules.restrictScalars
            (Functor.whiskerRight (purTwistIntegralCompletionMap S l E).hom
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj
                  (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
                    (purTwistCompletedScalarMap S l E) (purTwistZlModule S l))).obj U))
      { toFun := fun x ↦ (1 :
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U)
            ⊗ₜ[(purTwistZlCompletion S l).obj.obj U,
              ((purTwistCompletedScalarMap S l E).hom.app U).hom]
                (show (purTwistZlModule S l).val.obj U from x)
        map_add' := by intros; rw [TensorProduct.tmul_add]
        map_smul' := by
          intro a x
          change (purTwistZlModule S l).val.obj U at x
          let c := ((purTwistCompletedScalarMap S l E).hom.app U).hom
          let aa := ((purTwistZlCompletionMap S l).hom.app U).hom
          let bb := ((purTwistConstantIntegersMap S l E).hom.app U).hom
          let dd := ((purTwistIntegralCompletionMap S l E).hom.app U).hom
          let := c.toAlgebra
          change (1 :
            (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U)
            ⊗ₜ[(purTwistZlCompletion S l).obj.obj U] (aa a • x) =
              (dd (bb a) * 1) ⊗ₜ[(purTwistZlCompletion S l).obj.obj U] x
          rw [TensorProduct.tmul_smul]
          change (c (aa a) * 1) ⊗ₜ[(purTwistZlCompletion S l).obj.obj U] x = _
          congr 2
          exact RingHom.congr_fun
            (congrArg (fun f : purTwistZlConstant S l ⟶
              WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S ↦
                (f.hom.app U).hom) (purTwistCoefficientSquare S l E)) a })

private theorem integralRawForwardApp_tmul
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    integralRawForwardApp S l E U
      (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U,
        ((purTwistConstantIntegersMap S l E).hom.app U).hom]
          (show ((SheafOfModules.restrictScalars.{u + 1}
            ((sheafCompose (ProEt.topology S)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)).val.obj U from x)) =
      (purTwistIntegralCompletionMap S l E).hom.app U b
        ⊗ₜ[(purTwistZlCompletion S l).obj.obj U,
          ((purTwistCompletedScalarMap S l E).hom.app U).hom] x := by
  change (((purTwistIntegralCompletionMap S l E).hom.app U b) * 1)
    ⊗ₜ[(purTwistZlCompletion S l).obj.obj U,
      ((purTwistCompletedScalarMap S l E).hom.app U).hom] x = _
  rw [mul_one]

attribute [local irreducible] integralRawForwardApp

private noncomputable def integralRawForward
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistConstantIntegersMap S l E)
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)) ⟶
      (_root_.PresheafOfModules.restrictScalars
        (Functor.whiskerRight (purTwistIntegralCompletionMap S l E).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj
        (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistCompletedScalarMap S l E) (purTwistZlModule S l)) where
  app U := integralRawForwardApp S l E U
  naturality := by
    intro U V f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    simp only [ModuleCat.comp_apply]
    change (integralRawForwardApp S l E V)
      (SheafOfModules.changeOfRingsMapOfUniverses
        (purTwistConstantIntegersMap S l E)
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)) f
            ((1 : (purTwistIntegralConstant S l E).obj.obj U) ⊗ₜ[_, _] x)) =
      SheafOfModules.changeOfRingsMapOfUniverses
        (purTwistCompletedScalarMap S l E) (purTwistZlModule S l) f
          ((integralRawForwardApp S l E U)
            ((1 : (purTwistIntegralConstant S l E).obj.obj U) ⊗ₜ[_, _] x))
    have hb := SheafOfModules.changeOfRingsMap_tmulOfUniverses.{u, u + 1, u + 1, u + 1}
      (purTwistConstantIntegersMap S l E)
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)) f 1 x
    rw [hb, map_one]
    change (purTwistZlModule S l).val.obj U at x
    have hV := integralRawForwardApp_tmul S l E V 1
      ((purTwistZlModule S l).val.map f x)
    have hU := congrArg
      (fun z ↦ SheafOfModules.changeOfRingsMapOfUniverses
        (purTwistCompletedScalarMap S l E) (purTwistZlModule S l) f z)
      (integralRawForwardApp_tmul S l E U 1 x)
    have hc := SheafOfModules.changeOfRingsMap_tmulOfUniverses.{u, u + 1, u + 1, u + 1}
      (purTwistCompletedScalarMap S l E) (purTwistZlModule S l) f
        ((purTwistIntegralCompletionMap S l E).hom.app U 1) x
    apply hV.trans
    apply Eq.trans _ (hU.trans hc).symm
    simp only [map_one]

private theorem integralRawForward_tmul
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    (integralRawForward S l E).app U
      (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U,
        ((purTwistConstantIntegersMap S l E).hom.app U).hom]
          (show ((SheafOfModules.restrictScalars.{u + 1}
            ((sheafCompose (ProEt.topology S)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)).val.obj U from x)) =
      (purTwistIntegralCompletionMap S l E).hom.app U b
        ⊗ₜ[(purTwistZlCompletion S l).obj.obj U,
          ((purTwistCompletedScalarMap S l E).hom.app U).hom] x := by
  exact integralRawForwardApp_tmul S l E U b x

private theorem integralRawForward_isIso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsIso (integralRawForward S l E) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.PresheafOfModules.toPresheaf _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  let a := ((purTwistZlCompletionMap S l).hom.app U).hom
  let b := ((purTwistConstantIntegersMap S l E).hom.app U).hom
  let c := ((purTwistCompletedScalarMap S l E).hom.app U).hom
  let d := ((purTwistIntegralCompletionMap S l E).hom.app U).hom
  let q :=
    letI := b.toAlgebra
    letI := a.toAlgebra
    RingEquiv.ofBijective (purTwistCoefficientTensorMap S l E U)
      (purTwistCoefficientTensor S l E U)
  have hsq : d.comp b = c.comp a :=
    congrArg (fun f ↦ (f.hom.app U).hom) (purTwistCoefficientSquare S l E).symm
  let e := pushoutModuleEquiv (M := (purTwistZlModule S l).val.obj U)
    a b c d hsq q (fun _ _ ↦ rfl)
  have he : ⇑((integralRawForward S l E).app U) = e := by
    funext z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s x =>
      change (purTwistZlModule S l).val.obj U at x
      exact (integralRawForward_tmul S l E U s x).trans
        (pushoutModuleEquiv_tmul a b c d hsq q (fun _ _ ↦ rfl) s x).symm
  change Function.Bijective ((integralRawForward S l E).app U)
  rw [he]
  exact e.bijective

attribute [local irreducible] integralRawForward

private noncomputable def integralDiscreteIso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    purTwistIntegralOne S l E ≅ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistIntegralCompletionMap S l E))).obj
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistCompletedScalarMap S l E) (purTwistZlModule S l)) := by
  have := integralRawForward_isIso S l E
  let d := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistIntegralCompletionMap S l E)
  let P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistCompletedScalarMap S l E) (purTwistZlModule S l)
  have := restrictionSheafificationComparison_isIso d P
  exact (_root_.PresheafOfModules.sheafification (𝟙 _)).mapIso
    (asIso (integralRawForward S l E)) ≪≫ asIso (restrictionSheafificationComparison d P)

private theorem integralDiscreteIso_tmul
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
    (x : ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)).val.obj U) :
    (integralDiscreteIso S l E).hom.val.app U (purTwistIntegralTensor S l E U b x) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (purTwistCompletedScalarMap S l E) (purTwistZlModule S l) U
          ((purTwistIntegralCompletionMap S l E).hom.app U b) x := by
  let d := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistIntegralCompletionMap S l E)
  let P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistCompletedScalarMap S l E) (purTwistZlModule S l)
  have h := sheafification_restrict_map_unit d (integralRawForward S l E) U
    (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U,
      ((purTwistConstantIntegersMap S l E).hom.app U).hom] x)
  exact h.trans (congrArg
    (((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 ((WeilConjectures.completedIntegralCommRingSheafUnrestricted
        l E S).obj ⋙ forget₂ CommRingCat RingCat))).unit.app P).app U)
      (integralRawForward_tmul S l E U b x))

attribute [local irreducible] integralDiscreteIso

private theorem integralExtensionReverse_isIso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsIso (integralExtensionReverse S l E) := by
  let F := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistIntegralCompletionMap S l E))
  have he : (integralDiscreteIso S l E).hom ≫
      F.map (integralExtensionReverse S l E) ≫ (integralForgetIso S l E).hom = 𝟙 _ := by
    apply SheafOfModules.scalarExtension_hom_ext (purTwistConstantIntegersMap S l E)
    intro U b x
    simp only [SheafOfModules.comp_val, _root_.PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    change (integralForgetIso S l E).hom.val.app U
      ((integralExtensionReverse S l E).val.app U
        ((integralDiscreteIso S l E).hom.val.app U
          (purTwistIntegralTensor S l E U b x))) = purTwistIntegralTensor S l E U b x
    rw [integralForgetIso_hom_apply]
    change (integralExtensionReverse S l E).val.app U
      ((integralDiscreteIso S l E).hom.val.app U (purTwistIntegralTensor S l E U b x)) =
        purTwistIntegralTensor S l E U b x
    rw [integralDiscreteIso_tmul]
    change (purTwistZlModule S l).val.obj U at x
    rw [integralExtensionReverse_section]
    apply ((purTwistIntegralAction_existsUnique S l E).exists.choose_spec.2.1
      U b (purTwistIntegralTensor S l E U 1 x)).trans
    exact (SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
      (purTwistConstantIntegersMap S l E)
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)) U b 1 x).trans
        (congrArg (fun z ↦ purTwistIntegralTensor S l E U z x) (mul_one b))
  have hh : F.map (integralExtensionReverse S l E) =
      (integralDiscreteIso S l E).inv ≫ (integralForgetIso S l E).inv := by
    rw [← cancel_epi (integralDiscreteIso S l E).hom, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp, ← cancel_mono (integralForgetIso S l E).hom]
    simpa only [Category.assoc, Iso.inv_hom_id] using he
  have : IsIso (F.map (integralExtensionReverse S l E)) := by rw [hh]; infer_instance
  have : IsIso ((SheafOfModules.toSheaf _).map (integralExtensionReverse S l E)) :=
    show IsIso ((SheafOfModules.toSheaf _).map
      (F.map (integralExtensionReverse S l E))) from Functor.map_isIso _ _
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

private theorem lifted_principal_kernel
    {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (a : R) (hs : Function.Surjective f)
    (hk : RingHom.ker f = Ideal.span {a}) :
    let g : ULift.{u + 1} R →+* ULift.{u + 1} T :=
      ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)
    Function.Surjective g ∧ RingHom.ker g = Ideal.span {ULift.up a} := by
  dsimp only
  constructor
  · intro t
    obtain ⟨r, hr⟩ := hs t.down
    exact ⟨ULift.up r, ULift.ext hr⟩
  · ext r
    change (ULift.up (f r.down) : ULift.{u + 1} T) = 0 ↔ _
    rw [show (ULift.up (f r.down) : ULift.{u + 1} T) = 0 ↔ f r.down = 0 from
      ULift.ringEquiv.injective.eq_iff.symm]
    change r.down ∈ RingHom.ker f ↔ _
    rw [hk, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨ULift.up b, ULift.ext hb⟩
    · rintro ⟨b, hb⟩
      exact ⟨b.down, congrArg ULift.down hb⟩

private noncomputable def integralUniformizerSection
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) : (purTwistIntegralConstant S l E).obj.obj U :=
  (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app U
      (ULift.up (Padic.coefficientExtensionUniformizer l E))

private theorem integralQuotient_sections
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) (n : ℕ) :
    Function.Surjective ((purTwistIntegralQuotient S l E n).hom.app U) ∧
      RingHom.ker ((purTwistIntegralQuotient S l E n).hom.app U).hom =
        (Ideal.span {integralUniformizerSection S l E U}) ^ (n + 1) := by
  let O := Padic.coefficientExtensionIntegers l E
  let K := Padic.coefficientExtensionIdeal l E (n + 1)
  have hk : RingHom.ker (Ideal.Quotient.mk K) =
      Ideal.span {(Padic.coefficientExtensionUniformizer l E) ^ (n + 1)} := by
    rw [Ideal.mk_ker]
    exact (Ideal.span_singleton_pow (Padic.coefficientExtensionUniformizer l E)
      (n + 1))
  obtain ⟨hs, hk⟩ := lifted_principal_kernel (Ideal.Quotient.mk K)
    ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1))
      Ideal.Quotient.mk_surjective hk
  let R := ULift.{u + 1} O
  let T := ULift.{u + 1} (O ⧸ K)
  let : TopologicalSpace R := ⊥
  let : TopologicalSpace T := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : DiscreteTopology T := ⟨rfl⟩
  let g : R →+* T := ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.mk K).comp ULift.ringEquiv.toRingHom)
  obtain ⟨hs', hk'⟩ := constantSection_principal_quotient S g
    (ULift.up ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1))) hs hk U
  refine ⟨hs', ?_⟩
  ext b
  change ((constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom g)).hom.app U b = 0 ↔ _
  rw [hk', Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hp : (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
      (CommRingCat.of R))).app U
        (ULift.up ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1))) =
      (integralUniformizerSection S l E U) ^ (n + 1) := by
    exact map_pow ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R))).app U).hom
        (ULift.up (Padic.coefficientExtensionUniformizer l E)) (n + 1)
  rw [hp]
  exact ⟨fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩, fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩⟩

-- Identify the positive quotient tower, including its distinguished maps, with completion.
private theorem integralUniformizerCompletion
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) :
    let B := (purTwistIntegralConstant S l E).obj.obj U
    let J : Ideal B := Ideal.span {integralUniformizerSection S l E U}
    ∃ i : AdicCompletion J B ≃+*
        (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U,
      (∀ b : B, i (AdicCompletion.of J B b) =
        (purTwistIntegralCompletionMap S l E).hom.app U b) ∧
      ∀ n : ℕ, ∃ r : B ⧸ J ^ (n + 1) ≃+*
          (WeilConjectures.integralCoefficientCommRingSheaf l E S n).obj.obj U,
        (∀ b : B, r (Ideal.Quotient.mk _ b) =
          (purTwistIntegralQuotient S l E n).hom.app U b) ∧
        ∀ x, (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U
          (i x) = r (AdicCompletion.evalₐ J (n + 1) x) := by
  let B := (purTwistIntegralConstant S l E).obj.obj U
  let J : Ideal B := Ideal.span {integralUniformizerSection S l E U}
  let ev := sheafToPresheaf (ProEt.topology S) RingCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  let evc := sheafToPresheaf (ProEt.topology S) CommRingCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U ⋙ forget₂ CommRingCat RingCat
  let D := WeilConjectures.integralCoefficientSheafSystem l E S ⋙ ev
  let c := ev.mapCone (limit.cone (WeilConjectures.integralCoefficientSheafSystem l E S))
  have hc : IsLimit c := isLimitOfPreserves ev (limit.isLimit _)
  let q : (Functor.const ℕᵒᵖ).obj (RingCat.of B) ⟶ D :=
    (Functor.const ℕᵒᵖ).map (evc.map (purTwistIntegralCompletionMap S l E)) ≫ c.π
  have hq (n : ℕ) : (q.app (op n)).hom =
      ((purTwistIntegralQuotient S l E n).hom.app U).hom :=
    congrArg (fun g ↦ (g.hom.app U).hom)
      ((purTwistIntegralCompletionMap_existsUnique S l E).exists.choose_spec n)
  have hdata (n : ℕ) : Function.Surjective (q.app (op n)) ∧
      RingHom.ker (q.app (op n)).hom = J ^ (n + 1) := by
    change Function.Surjective (q.app (op n)).hom ∧ _
    rw [hq]
    exact integralQuotient_sections S l E U n
  obtain ⟨i, hi⟩ := completion_positive_iso_normalized J D c hc q
    (fun n ↦ (hdata n).1) (fun n ↦ (hdata n).2)
  refine ⟨i, ?_, ?_⟩
  · intro b
    apply Concrete.isLimit_ext D hc
    intro n
    obtain ⟨r, hr, hp⟩ := hi n.unop
    change c.π.app n (i (AdicCompletion.of J B b)) =
      c.π.app n ((purTwistIntegralCompletionMap S l E).hom.app U b)
    rw [hp, AdicCompletion.evalₐ_of, hr]
    rfl
  · intro n
    obtain ⟨r, hr, hp⟩ := hi n
    exact ⟨r, fun b ↦ (hr b).trans (RingHom.congr_fun (hq n) b), hp⟩

private theorem completion_eval_kernel
    {B : Type (u + 1)} [CommRing B] (J : Ideal B) (hJ : J.FG) (n : ℕ)
    (x : AdicCompletion J B) :
    AdicCompletion.evalₐ J n x = 0 ↔
      x ∈ (J ^ n).map (algebraMap B (AdicCompletion J B)) := by
  have he : AdicCompletion.evalₐ J n x = 0 ↔ AdicCompletion.eval J B n x = 0 := by
    unfold AdicCompletion.evalₐ
    rw [AlgHom.comp_apply]
    exact map_eq_zero_iff _ (AlgEquiv.injective _)
  rw [he, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hJ]
  simp only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]

private theorem integralProjection_kernel
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) (n : ℕ) :
    RingHom.ker
        ((WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U).hom =
      (RingHom.ker ((purTwistIntegralQuotient S l E n).hom.app U).hom).map
        ((purTwistIntegralCompletionMap S l E).hom.app U).hom := by
  let B := (purTwistIntegralConstant S l E).obj.obj U
  let J : Ideal B := Ideal.span {integralUniformizerSection S l E U}
  obtain ⟨i, hi, hlevels⟩ := integralUniformizerCompletion S l E U
  obtain ⟨r, hr, hp⟩ := hlevels n
  rw [(integralQuotient_sections S l E U n).2]
  have hd : ((purTwistIntegralCompletionMap S l E).hom.app U).hom =
      i.toRingHom.comp (algebraMap B (AdicCompletion J B)) := by
    ext b
    exact (hi b).symm
  rw [hd, ← Ideal.map_map]
  ext y
  obtain ⟨x, rfl⟩ := i.surjective y
  rw [RingHom.mem_ker, hp, map_eq_zero_iff r r.injective,
    completion_eval_kernel J (Submodule.fg_span_singleton _) (n + 1)]
  constructor
  · intro hx
    exact (Ideal.mem_map_iff_of_surjective i.toRingHom i.surjective).mpr ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨z, hz, he⟩ := (Ideal.mem_map_iff_of_surjective i.toRingHom i.surjective).mp hx
    exact i.injective he ▸ hz

-- Finite targets see the same linear maps before and after completion.
section QuotientTransport
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
private abbrev LocalMod (R : Sheaf J CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
private noncomputable abbrev localRes {R T : Sheaf J CommRingCat.{u + 1}} (f : R ⟶ T) :=
  SheafOfModules.restrictScalars.{u + 1} ((sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f)
private noncomputable abbrev localChange {R T : Sheaf J CommRingCat.{u + 1}}
    (f : R ⟶ T) := PurScalar.tensorFunctor f
variable {R B T Q : Sheaf J CommRingCat.{u + 1}}
private noncomputable def localResCompIso
    (φ : R ⟶ B) (p : B ⟶ T) (q : R ⟶ T) (h : φ ≫ p = q) :
    localRes p ⋙ localRes φ ≅ localRes q := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine { hom := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             inv := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · exact ModuleCat.ofHom
        (X := ((localRes φ).obj ((localRes p).obj N)).val.obj U)
        (Y := ((localRes q).obj N).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by intros; subst q; rfl }
    · intros; ext; rfl
    · exact ModuleCat.ofHom
        (X := ((localRes q).obj N).val.obj U)
        (Y := ((localRes φ).obj ((localRes p).obj N)).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by intros; subst q; rfl }
    · intros; ext; rfl
    · ext; rfl
    · ext; rfl
  · intros; ext; rfl
private theorem scalarLinear_of_kernel_span
    {R B S : Type (u + 1)} [CommRing R] [CommRing B] [CommRing S]
    (φ : R →+* B) (q : R →+* S) (p : B →+* S)
    (h : p.comp φ = q) (hq : Function.Surjective q)
    (hk : RingHom.ker p = Ideal.span (φ '' (RingHom.ker q : Set R)))
    (M : ModuleCat B) (N : ModuleCat S)
    (f : (ModuleCat.restrictScalars φ).obj M ⟶ (ModuleCat.restrictScalars q).obj N)
    (b : B) (m : M) : f (b • m) = p b • f m := by
  have hz (d : B) (hd : d ∈ RingHom.ker p) : ∀ m : M, f (d • m) = 0 := by
    rw [hk] at hd
    change d ∈ Submodule.span B (φ '' (RingHom.ker q : Set R)) at hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨a, ha, rfl⟩ := hd
      intro m
      have hf := f.hom.map_smul a m
      change f (φ a • m) = q a • f m at hf
      rw [show q a = 0 from ha, zero_smul] at hf
      exact hf
    | zero => intro m; simp only [zero_smul, map_zero]
    | add d e hd he ihd ihe =>
      intro m
      rw [add_smul, map_add, ihd, ihe, add_zero]
    | smul a d hd ih =>
      intro m
      change f ((a * d) • m) = 0
      rw [mul_comm a d, mul_smul]
      exact ih (a • m)
  obtain ⟨a, ha⟩ := hq (p b)
  have hφ (a : R) : p (φ a) = q a := congrArg (fun f : R →+* S ↦ f a) h
  have hd : b - φ a ∈ RingHom.ker p := by
    change p (b - φ a) = 0
    rw [map_sub, hφ, ha, sub_self]
  have he := hz (b - φ a) hd m
  rw [sub_smul, map_sub] at he
  rw [sub_eq_zero] at he
  rw [he]
  have hf := f.hom.map_smul a m
  change f (φ a • m) = q a • f m at hf
  exact hf.trans (congrArg (fun s : S ↦ s • f m) ha)

private noncomputable def quotientRestrictionHomEquiv (φ : R ⟶ B) (q : R ⟶ Q) (p : B ⟶ Q)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _)))
    (M : LocalMod B) (N : LocalMod Q) :
    ((localRes φ).obj M ⟶ (localRes q).obj N) ≃ (M ⟶ (localRes p).obj N) where
  toFun f :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := M.val.obj U) (Y := ((localRes p).obj N).val.obj U)
            { toFun := fun m ↦ f.val.app U m
              map_add' := fun x y ↦ (f.val.app U).hom.map_add x y
              map_smul' := fun b m ↦ scalarLinear_of_kernel_span
                (φ.hom.app U).hom (q.hom.app U).hom (p.hom.app U).hom
                (congrArg (fun t : R ⟶ Q ↦ (t.hom.app U).hom) h)
                (hq U) (hk U) (M.val.obj U) (N.val.obj U) (f.val.app U) b m }
          naturality := by
            intro U V i
            ext m
            exact congrArg (fun t ↦ t m) (f.val.naturality i) } }
  invFun g := (localRes φ).map g ≫ (localResCompIso φ p q h).hom.app N
  left_inv f := by subst q; ext U m; rfl
  right_inv f := by subst q; ext U m; rfl

private noncomputable def quotientTensorAdjunction (φ : R ⟶ B) (q : R ⟶ Q) (p : B ⟶ Q)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _))) :
    localRes φ ⋙ localChange q ⊣ localRes p :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦ (PurScalar.tensorHomEquiv q _ _).trans
        (quotientRestrictionHomEquiv φ q p h hq hk M N)
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        change (PurScalar.tensorHomEquiv q _ _).symm
          ((quotientRestrictionHomEquiv φ q p h hq hk M N).symm (f ≫ g)) = _
        have hh : (quotientRestrictionHomEquiv φ q p h hq hk M N).symm (f ≫ g) =
            (localRes φ).map f ≫ (quotientRestrictionHomEquiv φ q p h hq hk M' N).symm g := by
          subst q
          ext U m
          rfl
        rw [hh]
        have hn := (PurScalar.tensorAdjunction q)
          |>.homEquiv_naturality_left_symm ((localRes φ).map f)
            ((quotientRestrictionHomEquiv φ q p h hq hk M' N).symm g)
        simp only [PurScalar.tensorAdjunction,
          Adjunction.mkOfHomEquiv_homEquiv] at hn
        exact hn
      homEquiv_naturality_right := by
        intro M N N' f g
        change (quotientRestrictionHomEquiv φ q p h hq hk M N')
          (PurScalar.tensorHomEquiv q _ _ (f ≫ g)) = _
        have hn := (PurScalar.tensorAdjunction q).homEquiv_naturality_right f g
        simp only [PurScalar.tensorAdjunction,
          Adjunction.mkOfHomEquiv_homEquiv] at hn
        rw [hn]
        rfl }

private noncomputable def quotientReductionIso
    (φ : R ⟶ B) (q : R ⟶ Q) (p : B ⟶ Q) (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _)))
    (M : LocalMod B) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} q
        ((localRes φ).obj M) ≅
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} p M :=
  (Adjunction.leftAdjointUniq (quotientTensorAdjunction φ q p h hq hk)
    (PurScalar.tensorAdjunction p)).app M
end QuotientTransport

private noncomputable def integralFiniteIso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
        (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n := by
  let e := quotientReductionIso (purTwistIntegralCompletionMap S l E)
    (purTwistIntegralQuotient S l E n)
    (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
    ((purTwistIntegralCompletionMap_existsUnique S l E).exists.choose_spec n)
    (fun U ↦ (integralQuotient_sections S l E U n).1)
    (fun U ↦ by
      rw [← Ideal.map_span, Ideal.span_eq]
      exact integralProjection_kernel S l E U n)
    (purTwistIntegralModule S l E)
  exact e.symm ≪≫ (PurScalar.tensorFunctor (purTwistIntegralQuotient S l E n)).mapIso
    (integralForgetIso S l E)

private theorem rankOne_cover
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (M : SheafOfModules.{u + 1} R)
    [∀ U, HasSheafify ((ProEt.topology S).over U) AddCommGrpCat.{u + 1}]
    [∀ U, ((ProEt.topology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (hM : M.IsFiniteLocallyFreeOfRank 1) :
    ∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      ∀ i, Nonempty (M.over (U i) ≅ (SheafOfModules.unit R).over (U i)) := by
  classical
  obtain ⟨I, X, hX, he⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := M) (r := 1)).mp hM
  obtain ⟨P, hP, hsub⟩ := ProEt.mem_topology_iff.mp (hX (ProEt.mk (𝟙 S)))
  let K := Σ V : S.ProEt, {g : V ⟶ ProEt.mk (𝟙 S) // P g}
  let U : K → S.ProEt := fun k ↦ k.1
  let f : ∀ k, U k ⟶ ProEt.mk (𝟙 S) := fun k ↦ k.2.val
  have hpres : Presieve.ofArrows U f = P := by
    funext V g
    apply propext
    constructor
    · rintro ⟨k⟩
      exact k.2.property
    · intro hg
      exact Presieve.ofArrows.mk (Y := U) (f := f) (⟨V, ⟨g, hg⟩⟩ : K)
  refine ⟨K, U, f, hpres.symm ▸ hP, fun k ↦ ?_⟩
  obtain ⟨i, ⟨g⟩⟩ := hsub k.1 k.2.val k.2.property
  let e := (he i).some ≪≫ SheafOfModules.freeUniqueIso _
  exact ⟨((SheafOfModules.overFunctorMap R g).app M).symm ≪≫
    (SheafOfModules.overMap R g).mapIso e ≪≫ SheafOfModules.overMapUnitIso (R := R) g⟩

private theorem finiteCoefficient_ne_zero
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (U : S.ProEt) (x : U.left) :
    (1 : (WeilConjectures.integralCoefficientSheaf l E S n).obj.obj (op U)) ≠ 0 := by
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  let π := Padic.coefficientExtensionUniformizer l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsLocalRing O := h.2.2.2.1
  let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  have hπ : Ideal.span ({π} : Set O) = m :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : IsLocalRing.maximalIdeal O = m :=
    h.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal O)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hm.trans hπ.symm)
  have hK : Padic.coefficientExtensionIdeal l E (n + 1) ≠ ⊤ := by
    change (Ideal.span ({π} : Set O)) ^ (n + 1) ≠ ⊤
    intro heq
    have hu := (Ideal.pow_eq_top_iff.mp heq).resolve_right (Nat.succ_ne_zero n)
    exact hirr.not_isUnit (Ideal.span_singleton_eq_top.mp hu)
  let : Nontrivial (Padic.coefficientExtensionRing l E (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr hK
  let R := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  obtain ⟨e, he⟩ := discreteCoefficientComparison S R
  intro hz
  have hz' := congrArg (fun a ↦ (e.hom.hom.app (op U) a).down x) hz
  rw [map_one, map_zero] at hz'
  change (1 : R) = 0 at hz'
  exact one_ne_zero hz'

-- A point on a covering member detects the unit section.
private theorem finiteLocalModel_nonzero
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) {I : Type (u + 1)} (U : I → S.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _)
    (he : ∀ i, Nonempty ((purTwistFiniteOne S l E n).over (U i) ≅
      (SheafOfModules.unit (WeilConjectures.integralCoefficientSheaf l E S n)).over (U i))) :
    Nonempty S → ¬IsZero (purTwistFiniteOne S l E n) := by
  rintro ⟨s⟩ hz
  have hc' := (ProEt.mem_precoverage_iff.mp hc)
  rw [Presieve.map_ofArrows] at hc'
  have hj := (Scheme.ofArrows_mem_precoverage_iff (@WeaklyEtale)).mp hc'.2
  obtain ⟨i, x, hx⟩ := hj.1 s
  let e := (he i).some
  let W := op (Over.mk (𝟙 (U i)))
  have hid : (𝟙 (purTwistFiniteOne S l E n) :
      purTwistFiniteOne S l E n ⟶ purTwistFiniteOne S l E n) = 0 := hz.eq_of_src _ _
  let one : (WeilConjectures.integralCoefficientSheaf l E S n).obj.obj (op (U i)) := 1
  have hy : e.inv.val.app W one = 0 :=
    congrArg (fun g ↦ g.val.app (op (U i)) (e.inv.val.app W one)) hid
  have hone := congrArg (fun g ↦ g.val.app W one) e.inv_hom_id
  apply finiteCoefficient_ne_zero S l E n (U i) x
  change e.hom.val.app W (e.inv.val.app W one) = one at hone
  exact hone.symm.trans ((congrArg (e.hom.val.app W) hy).trans
    ((e.hom.val.app W).hom.map_zero))

/-- Scalar extension of the completed root line has local bases and ordinary
finite quotients with finite étale local models. -/
theorem purTwistIntegralLocalModels
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [∀ x : S, Invertible (l : S.residueField x)]
    (hL : (purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1) :
    (∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      ∀ i, Nonempty ((purTwistIntegralModule S l E).over (U i) ≅
        (SheafOfModules.unit
          (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S)).over (U i))) ∧
    ∀ n : ℕ,
      Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
          (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n) ∧
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i, Nonempty ((purTwistFiniteOne S l E n).over (U i) ≅
          (SheafOfModules.unit (WeilConjectures.integralCoefficientSheaf l E S n)).over (U i))) ∧
      (Nonempty S → ¬IsZero (purTwistFiniteOne S l E n)) := by
  classical
  have (U : S.ProEt) : EssentiallySmall.{u + 1} (Over U) :=
    essentiallySmallSelf.{0, u, u + 1} _
  have (U : S.ProEt) :
      ((ProEt.topology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  have (U : S.ProEt) :
      HasSheafify ((ProEt.topology S).over U) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  obtain ⟨I, U, f, hc, he⟩ := rankOne_cover S _ (purTwistZlModule S l) hL
  have := integralExtensionReverse_isIso S l E
  let ei := asIso (integralExtensionReverse S l E)
  have hb (i : I) : Nonempty ((purTwistIntegralModule S l E).over (U i) ≅
      (SheafOfModules.unit
        (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S)).over (U i)) :=
    ⟨(SheafOfModules.overFunctor _ (U i)).mapIso ei.symm ≪≫
      SheafOfModules.extendedBasisIso (purTwistCompletedScalarMap S l E)
        (purTwistZlModule S l) (he i).some⟩
  refine ⟨⟨I, U, f, hc, hb⟩, fun n ↦ ?_⟩
  let en := integralFiniteIso S l E n
  have hn (i : I) : Nonempty ((purTwistFiniteOne S l E n).over (U i) ≅
      (SheafOfModules.unit
        (WeilConjectures.integralCoefficientSheaf l E S n)).over (U i)) :=
    ⟨(SheafOfModules.overFunctor _ (U i)).mapIso en.symm ≪≫
      SheafOfModules.extendedBasisIso
        (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
        (purTwistIntegralModule S l E) (hb i).some⟩
  exact ⟨⟨en⟩, ⟨I, U, f, hc, hn⟩, finiteLocalModel_nonzero S l E n U f hc hn⟩

end AlgebraicGeometry.Scheme
