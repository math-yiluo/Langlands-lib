/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame

/-! # From a realized Ext class to its arrow

Source: diagonal coefficient changes (1).
(blueprint: lem-diagonal-finite-cartier-class-to-arrow).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] geoCartierConstant geoCartierLine finiteRealizedClass

/-- Applying the Ext-to-derived-Hom equivalence gives precisely the normalized
Cartier-arrow equation. No coefficient or endpoint data are changed.
Source: diagonal coefficient changes (1).
(blueprint: lem-diagonal-finite-cartier-class-to-arrow).
Proof: apply the Hom equivalence to the equality of classes, cancel its inverse
in the explicitly constructed finite realization, and unfold the canonical arrow. -/
theorem finiteCartierArrowEquation_of_class
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hW : IsUnit (N : Γ(diagonalSurface Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eW : FiniteRealization R A (diagonalSurface Y))
    (line : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
    (s : eW.F.obj (source R Y) ≅
      (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (h : finiteRealizedClass N hA Y eW line s d.delta =
      geoCartierCanonicalClass A N hN hA (diagonalImmersion Y)
        (diagonalImmersion_cartier Y) hW) :
    FiniteCartierArrowEquation R A N hN hA Y hW L d eW line s := by
  unfold FiniteCartierArrowEquation finiteCartierArrow SpTowerClasses.extensionArrow
  unfold finiteRealizedClass at h
  exact Ext.homEquiv.symm_apply_eq.mp h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
