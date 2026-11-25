/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # The constant-to-supported completed diagonal coefficient map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

/-- The ordinary constant-to-supported map induced by the completed coefficient map.
Source: diagonal tower trace proof (2), forgetting support of the diagonal divisor.
(blueprint: def-sfb-diagonal-trace-completed-supported-unit). -/
def completedSupportedUnit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    SheafOfModules.unit.{u, u + 1, u + 1}
      (Scheme.purTwistRing (diagonalSurface Y)
        (Scheme.purTwistZlCompletion (diagonalSurface Y) l)) ⟶
      diagonalCompletedSource l Y := by
  let unitToPushforwardRestrictedUnit
      {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D}
      {F : C ⥤ D} [F.IsContinuous J K]
      {R : Sheaf J RingCat.{u + 1}} {S T : Sheaf K RingCat.{u + 1}}
      (α : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S) (φ : S ⟶ T) :
      SheafOfModules.unit.{u, u + 1, u + 1} R ⟶
        (SheafOfModules.pushforward.{u + 1} α).obj
          ((SheafOfModules.restrictScalars φ).obj (SheafOfModules.unit T)) := by
    exact SheafOfModules.unitToPushforwardObjUnit
      (α ≫ (F.sheafPushforwardContinuous RingCat J K).map φ)
  unfold diagonalCompletedSource Scheme.proEtaleRingedDirectImage
  let i := diagonalImmersion Y
  let R := Scheme.purTwistZlCompletion (diagonalSurface Y) l
  exact unitToPushforwardRestrictedUnit
    (C := (diagonalSurface Y).ProEt) (D := (ProjectiveLine Y).ProEt)
    (J := Scheme.ProEt.topology (diagonalSurface Y))
    (K := Scheme.ProEt.topology (ProjectiveLine Y))
    (F := Scheme.proEtaleBaseChange i)
    (R := Scheme.purTwistRing (diagonalSurface Y) R)
    (S := Scheme.proEtaleModuleCoefficients
      ((Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R))
    (T := Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
    ⟨Functor.whiskerRight
      ((Scheme.proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (diagonalCompletedCoefficientMap l i))

end AlgebraicGeometry.ProEtale.DiagonalTrace
