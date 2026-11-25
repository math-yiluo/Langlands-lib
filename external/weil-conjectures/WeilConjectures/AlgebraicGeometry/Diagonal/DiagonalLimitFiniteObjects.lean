/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface

/-! # Named finite objects for the diagonal limit

These definitions spell out the existing specification with shared endpoint and
normalization functions. No coefficient object or boundary is changed.
(blueprint: def-sfb-diagonal-limit-finite-objects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The finite supported source, with its coefficient category fixed by name. -/
def diagonalLimitFiniteSource (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (n : ℕ) :
    DiagonalMod ℓ (diagonalSurface Y) :=
  (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
    ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
      (diagonalImmersion Y)).obj
        (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))

/-- The finite Tate target, with its coefficient category fixed by name. -/
def diagonalLimitFiniteTarget (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (n : ℕ) :
    DiagonalMod ℓ (diagonalSurface Y) :=
  (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
    (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y))

/-- The given finite Cartier class in its prescribed endpoint Ext group. -/
def diagonalLimitFiniteClass (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))] (n : ℕ) :
    Ext (diagonalLimitFiniteSource ℓ Y n) (diagonalLimitFiniteTarget ℓ Y n) 2 :=
  diagonalExactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
    (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1)
      (diagonalImmersion Y) (diagonalImmersion_cartier Y)
      (diagonalSurface_power_unit ℓ Y hY n))

/-- The root-tower identification used by the strict system. -/
def diagonalLimitRoots (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (H : DiagonalSystems ℓ (diagonalSurface Y)) :=
  H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
    Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime)

end AlgebraicGeometry.ProEtale
