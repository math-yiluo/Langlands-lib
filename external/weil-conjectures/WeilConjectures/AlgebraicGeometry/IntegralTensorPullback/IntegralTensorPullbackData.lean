/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficients
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullOrdinaryUnit
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement

/-!
# Strict comparison data for integral inverse image

The comparison is constructed on a strict reduction tower, with the quotient
augmentation and zero shifted coordinate. Constant scalar restriction retains a
separate coefficient category. Positive exponent n+1 is indexed by n: ℕ.

## Main definitions

* `comparison`: the quotient-augmented strict tower after integral inverse image.
* `constantComparison`: the Stacks completion unit over constant integral scalars.
* `restrictionPullback`: the scalar comparison normalized on tensor generators.

## Main statement

The final preservation theorem is assembled in `IntegralTensorPullback`.
These definitions are shared by its two independent normalization lemmas.

## References

* Stacks Tags 099I and 099N(2), (5)
* Stacks 08TC
* Stacks 099N(5)
* Stacks 099N(2), (5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u a b
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback

section Augmentation
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The strict augmentation has zero composite with 1 minus shift. -/
theorem augmentation_condition (P : CochainComplex A ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain P
        (∏ᶜ fun n : ℕ ↦ T.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (fun n ↦ γ.app (op n)) ≫
          towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
            (WeilConjectures.integralOperationsTowerStep T)) = 0 := by
  have h : Pi.lift (fun n ↦ γ.app (op n)) ≫
      towerTransitionEndomorphism (WeilConjectures.integralOperationsTowerStep T) = 0 := by
    apply Pi.hom_ext
    intro n
    have hn := γ.naturality (homOfLE (Nat.le_succ n)).op
    simp only [Functor.const_obj_map] at hn
    simp [towerTransitionEndomorphism, towerProductShift,
      WeilConjectures.integralOperationsTowerStep, Category.assoc, ← hn]
  simp [h, CochainComplex.HomComplex.Cochain.ofHom_zero]

/-- The strict map to the Roos complex, with quotient legs and zero homotopy. -/
def augmentation (P : CochainComplex A ℤ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    P ⟶ WeilConjectures.integralOperationsRoos T :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
            (WeilConjectures.integralOperationsTowerStep T))
    (Pi.lift (fun n ↦ γ.app (op n))) 0 (augmentation_condition P T γ)
end Augmentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing constant condensed ring on the point, for the integer scalar ring. -/
abbrev constantRing :=
  (sfbPointConstantRing.{u}.obj
    (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).X

/-- Constant scalar coefficients are commutative. -/
theorem constantRing_isCommMonObj : IsCommMonObj (constantRing l E) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact FiniteConstantModel.constantScalars_commutative
    (Padic.coefficientExtensionIntegers l E)
attribute [instance] constantRing_isCommMonObj

/-- The constant scalar map sends a scalar to its constant continuous function.
It is the actual sheafification-adjunction map, in the common coefficient universe. -/
def constantToIntegral : constantRing l E ⟶ DerivedNakayama.integerRing l E :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv _ _).symm
    { app S := AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up (ContinuousMap.const S.unop x.down)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

/-- The constant-function map preserves the coefficient unit and multiplication. -/
theorem constantToIntegral_isMonHom : IsMonHom (constantToIntegral l E) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact FiniteConstantModel.scalarToContinuous_isMonHom
    (Padic.coefficientExtensionIntegers l E)
attribute [instance] constantToIntegral_isMonHom

/-- Restrict an internal continuous integral module to its constant integral scalars.
This uses the recorded restriction-of-scalars operation on module objects. -/
abbrev restriction (X : Scheme.{u}) :
    AdicCompletion.Modules l E X ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (constantRing l E) X) :=
  Mod.comap ((upperStarFromPoint X).map (constantToIntegral l E))

/-- Constant-coefficient modules remain a distinct category from completed coefficients. -/
abbrev ConstantModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (constantRing l E) X)

/-- The strict integral reduction tower before applying inverse image. -/
def tower (Y : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (AdicCompletion.Modules l E Y) ℤ :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ (AdicCompletion.level l E Y n).obj P)
    (AdicCompletion.levelStep l E Y P)

private theorem quotientUnit_step (n : ℕ) :
    AdicCompletion.quotientUnit l E (n + 1) ≫ AdicCompletion.quotientStep l E n =
      AdicCompletion.quotientUnit l E n := by
  apply Mod.hom_ext
  rfl

private theorem finiteUnit_step (X : Scheme.{u}) (n : ℕ) :
    AdicCompletion.finiteUnit l E X (n + 1) ≫
      (DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n) =
      AdicCompletion.finiteUnit l E X n := by
  dsimp only [AdicCompletion.finiteUnit]
  rw [Category.assoc, ← Functor.map_comp, quotientUnit_step]

private theorem levelUnit_step (X : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
    AdicCompletion.levelUnit l E X P (n + 1) ≫ AdicCompletion.levelStep l E X P n =
      AdicCompletion.levelUnit l E X P n := by
  apply HomologicalComplex.hom_ext
  intro i
  change ((ρ_ (P.X i)).inv ≫ P.X i ◁ AdicCompletion.finiteUnit l E X (n + 1)) ≫
    P.X i ◁ (DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n) =
    (ρ_ (P.X i)).inv ≫ P.X i ◁ AdicCompletion.finiteUnit l E X n
  rw [Category.assoc, ← whiskerLeft_comp, finiteUnit_step]

/-- The quotient maps are a strict compatible augmentation of the reduction tower. -/
theorem towerUnit_compatible (Y : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj P).map (homOfLE (Nat.le_succ n)).op ≫
        AdicCompletion.levelUnit l E Y P n =
      AdicCompletion.levelUnit l E Y P (n + 1) ≫
        (tower l E Y P).map (homOfLE (Nat.le_succ n)).op := by
  change 𝟙 P ≫ AdicCompletion.levelUnit l E Y P n =
    AdicCompletion.levelUnit l E Y P (n + 1) ≫
      (tower l E Y P).map (homOfLE (Nat.le_succ n)).op
  rw [Category.id_comp]
  simpa only [tower, Functor.ofOpSequence_map_homOfLE_succ] using
    (levelUnit_step l E Y P n).symm

/-- The strict quotient augmentation, before inverse image. -/
def towerUnit (Y : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (Functor.const ℕᵒᵖ).obj P ⟶ tower l E Y P :=
  NatTrans.ofOpSequence (AdicCompletion.levelUnit l E Y P) (towerUnit_compatible l E Y P)

/-- Apply exact inverse image to the whole strict reduction tower. -/
def pulledTower {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :=
  tower l E Y P ⋙
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex (.up ℤ)

/-- The canonical comparison on a K-flat representative, using the strict quotient
augmentation and zero shifted coordinate, rather than a triangulated cone lift. -/
def comparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :=
  augmentation
    (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
      (.up ℤ)).obj P)
    (pulledTower l E g P)
    ((Functor.constComp ℕᵒᵖ P
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
        (.up ℤ))).inv ≫
      Functor.whiskerRight (towerUnit l E Y P)
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
          (.up ℤ)))

/-- The coefficient inclusion is linear as a map from the constant regular module
into the restricted integral regular module. -/
theorem constantUnit_linear (X : Scheme.{u}) :
    Mod.act (𝟙_ (ConstantModules l E X)).X ≫
        (upperStarFromPoint X).map (constantToIntegral l E) =
      condensedRingObj (constantRing l E) X ◁
          (upperStarFromPoint X).map (constantToIntegral l E) ≫
        Mod.act ((restriction l E X).obj (𝟙_ (AdicCompletion.Modules l E X))).X := by
  change MonObj.mul ≫ (upperStarFromPoint X).map (constantToIntegral l E) =
    condensedRingObj (constantRing l E) X ◁
      (upperStarFromPoint X).map (constantToIntegral l E) ≫
    ((upperStarFromPoint X).map (constantToIntegral l E) ▷
      condensedRingObj (DerivedNakayama.integerRing l E) X ≫ MonObj.mul)
  simpa only [tensorHom_def', Category.assoc] using
    (IsMonHom.mul_hom ((upperStarFromPoint X).map (constantToIntegral l E)))

/-- The canonical inclusion of the constant coefficient unit into the integral unit. -/
def constantUnit (X : Scheme.{u}) :
    𝟙_ (ConstantModules l E X) ⟶
      (restriction l E X).obj (𝟙_ (AdicCompletion.Modules l E X)) :=
  Mod.homMk ((upperStarFromPoint X).map (constantToIntegral l E)) (constantUnit_linear l E X)

/-- The same finite constant quotient, now with its constant integral scalar action.
Finite continuous coefficients are constant; only the integral scalar action changes. -/
abbrev constantFinite (X : Scheme.{u}) (n : ℕ) :=
  (restriction l E X).obj (AdicCompletion.finiteModule l E X n)

/-- Derived reduction over constant integral coefficients, computed on a K-flat complex. -/
abbrev constantLevel (X : Scheme.{u}) (n : ℕ) :=
  (tensorRight (constantFinite l E X n)).mapHomologicalComplex (.up ℤ)

/-- The transitions in the constant scalar reduction tower are the same quotient maps. -/
def constantStep (X : Scheme.{u}) (Q : CochainComplex (ConstantModules l E X) ℤ) (n : ℕ) :
    (constantLevel l E X (n + 1)).obj Q ⟶ (constantLevel l E X n).obj Q :=
  (NatTrans.mapHomologicalComplex
    ((tensoringRight (ConstantModules l E X)).map
      ((restriction l E X).map
        ((DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n))))
    (.up ℤ)).app Q

/-- Tensoring with the actual quotient of the constant coefficient unit. -/
def constantLevelUnit (X : Scheme.{u})
    (Q : CochainComplex (ConstantModules l E X) ℤ) (n : ℕ) :
    Q ⟶ (constantLevel l E X n).obj Q :=
  (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso (ConstantModules l E X)).inv ≫
      (tensoringRight (ConstantModules l E X)).map
        (constantUnit l E X ≫ (restriction l E X).map (AdicCompletion.finiteUnit l E X n)))
    (.up ℤ)).app Q

/-- The strict constant scalar reduction tower. -/
def constantTower (X : Scheme.{u}) (Q : CochainComplex (ConstantModules l E X) ℤ) :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ (constantLevel l E X n).obj Q)
    (constantStep l E X Q)

/-- Quotient augmentations commute with the constant scalar transitions. -/
theorem constantTowerUnit_compatible (X : Scheme.{u})
    (Q : CochainComplex (ConstantModules l E X) ℤ) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj Q).map (homOfLE (Nat.le_succ n)).op ≫
        constantLevelUnit l E X Q n =
      constantLevelUnit l E X Q (n + 1) ≫
        (constantTower l E X Q).map (homOfLE (Nat.le_succ n)).op := by
  simp only [Functor.const_obj_map, constantTower,
    Functor.ofOpSequence_map_homOfLE_succ]
  apply HomologicalComplex.hom_ext
  intro i
  change (ρ_ (Q.X i)).inv ≫ Q.X i ◁
      (constantUnit l E X ≫ (restriction l E X).map (AdicCompletion.finiteUnit l E X n)) =
    ((ρ_ (Q.X i)).inv ≫ Q.X i ◁
      (constantUnit l E X ≫
        (restriction l E X).map (AdicCompletion.finiteUnit l E X (n + 1)))) ≫
      Q.X i ◁ (restriction l E X).map
        ((DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n))
  rw [Category.assoc, ← whiskerLeft_comp, Category.assoc,
    ← Functor.map_comp, finiteUnit_step]

/-- The strict constant scalar quotient augmentation. -/
def constantTowerUnit (X : Scheme.{u}) (Q : CochainComplex (ConstantModules l E X) ℤ) :
    (Functor.const ℕᵒᵖ).obj Q ⟶ constantTower l E X Q :=
  NatTrans.ofOpSequence (constantLevelUnit l E X Q) (constantTowerUnit_compatible l E X Q)

/-- The exact constant coefficient inverse image applied to the whole reduction tower. -/
def constantPulledTower {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Q : CochainComplex (ConstantModules l E Y) ℤ) :=
  constantTower l E Y Q ⋙
    (CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)

/-- The Stacks completed inverse-image unit on a constant-coefficient K-flat model.
The target is the Roos model of Rlim of the pulled-back constant reductions. -/
def constantComparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Q : CochainComplex (ConstantModules l E Y) ℤ) :=
  augmentation
    (((CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)).obj Q)
    (constantPulledTower l E g Q)
    ((Functor.constComp ℕᵒᵖ Q
      ((CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ))).inv ≫
      Functor.whiskerRight (constantTowerUnit l E Y Q)
        ((CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)))

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
