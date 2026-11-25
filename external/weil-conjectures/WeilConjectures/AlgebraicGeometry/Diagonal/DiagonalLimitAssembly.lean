/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface

/-! # Completed diagonal limit assembly -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w a b c vc r
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- The complete normalized diagonal limit proposition.
Source: blueprint clauses 1 and 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def DiagonalCompletedLimitSpec (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))) :
    Prop :=
  DiagonalLimitDataSpec ℓ
    (diagonalScalarExtension ℓ (diagonalSurface Y)) D
    (diagonalIntegralSource Y) (diagonalComparisonUnits Y) (diagonalIntegralBoundary Y)
    (diagonalCompletedRestriction ℓ (diagonalSurface Y))
    (diagonalCompletedSource ℓ Y) (Scheme.purTwistZlModule (diagonalSurface Y) ℓ)
    (fun H : DiagonalSystems ℓ (diagonalSurface Y) ↦
      H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
        Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (fun (H : DiagonalSystems ℓ (diagonalSurface Y))
      (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
        Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
      (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2) ↦
    diagonalFiniteCycleNormalization
      (A := DiagonalMod ℓ (diagonalSurface Y))
      (D.ordinary.E.obj (diagonalIntegralSource Y)) H c
      (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
          (diagonalImmersion Y)).obj
            (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
      (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)))
      (fun n s ↦ DiagonalSourceNormalization ℓ Y D.ordinary n s)
      (fun n t ↦ HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (roots.hom.app (op n) ≫
          cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
            (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)))
      (fun n ↦ diagonalExactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
        (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1)
          (diagonalImmersion Y) (diagonalImmersion_cartier Y)
          (diagonalSurface_power_unit ℓ Y hY n)))
    )
        (fun s₀ ↦ ∀ n : ℕ,
          diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
            (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
          (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
            (diagonalForget ℓ (diagonalSurface Y)).map
              ((D.ordinary.π n).app (diagonalIntegralSource Y)))
    (fun (H : DiagonalSystems ℓ (diagonalSurface Y))
        (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
          Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime)) ↦
        (fun (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
            (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅
              limit (J := ℕᵒᵖ) (C := DiagonalMod ℓ (diagonalSurface Y)) H) ↦
          HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
          (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv))

end AlgebraicGeometry.ProEtale
