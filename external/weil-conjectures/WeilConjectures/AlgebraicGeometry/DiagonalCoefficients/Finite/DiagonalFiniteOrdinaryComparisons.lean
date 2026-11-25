/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteRealization

/-! # Ordinary finite comparisons at generic coefficients

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: def-diagonal-finite-ordinary-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R] (A : Type (u + 1)) [CommRing A]

/-- The supported coefficient comparison and its exact underlying normalization.
Source: coefficient changes (blueprint: def-diagonal-finite-ordinary-comparisons). -/
structure FiniteSourceComparison (Y : Scheme.{u})
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (eW : FiniteRealization R A (diagonalSurface Y)) where
  iso : eW.F.obj (source R Y) ≅
      (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y))
  normalization : HEq (eW.underlying.inv.app (source R Y) ≫
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map iso.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (Mod.regular (condensedRingObj R (ProjectiveLine Y))) ≫
          (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
            (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map eP.unitIso.hom))

/-- The ordinary direct-image square with its exact underlying normalization.
Source: coefficient changes (blueprint: def-diagonal-finite-ordinary-comparisons). -/
structure FiniteOrdinaryPushSquare {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : FiniteRealization R A X) (eS : FiniteRealization R A S) where
  ordinary : CondensedRing.lowerStar R f ⋙ eS.F ≅
    eX.F ⋙ lowerStar (ModuleCat.{u + 1} A) f
  normalization : ∀ M : Modules R X,
    HEq ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map (ordinary.hom.app M) ≫
      (lowerStar Ab.{u + 1} f).map (eX.underlying.hom.app M))
      (eS.underlying.hom.app ((CondensedRing.lowerStar R f).obj M))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
