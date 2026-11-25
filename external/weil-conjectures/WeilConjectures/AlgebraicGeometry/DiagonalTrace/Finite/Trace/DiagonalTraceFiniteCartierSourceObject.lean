/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface

/-! # Explicit finite Cartier coordinate objects -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The supported finite constant object in the fixed diagonal module category.
Source: diagonal trace proof (2), finite source projection.
(blueprint: def-sfb-diagonal-trace-finite-cartier-source-object). -/
abbrev finiteCartierSourceObject (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) :
    DiagonalMod l (diagonalSurface Y) :=
  (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
    ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
      (diagonalImmersion Y)).obj
        (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))

end AlgebraicGeometry.ProEtale.DiagonalTrace
