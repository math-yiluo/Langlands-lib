/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison

/-! # Fixed endpoints for a finite étale Ext class -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.mapExactFunctor
  comparisonUpperStar

/-- The constant comparison with both endpoint sheaves fixed explicitly.
Source: exact comparison preserves constant sheaves.
(blueprint: def-sfb-diagonal-trace-finite-etale-image). -/
@[irreducible] def finiteEtaleConstantIso (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
      (Etale.ordinaryFiniteConstant A T) ≅ geoCartierConstant A T :=
  (comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)

/-- The Tate-line comparison, with both endpoint sheaves fixed explicitly.
Source: the definition of the ordinary pro-etale finite Tate line.
(blueprint: def-sfb-diagonal-trace-finite-etale-image). -/
@[irreducible] def finiteEtaleLineIso (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
      (Scheme.finiteEtaleTateLine T N A hA) ≅ geoCartierLine A N hA T := Iso.refl _

/-- Exact comparison, with both ordinary pro-étale endpoints fixed.
Source: exact site comparison and endpoint transport.
(blueprint: def-sfb-diagonal-trace-finite-etale-image). -/
@[irreducible] def finiteEtaleProEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) :
    Ext (Etale.ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2 ≃
    Ext (geoCartierConstant A T) (geoCartierLine A N hA T) 2 :=
  (finiteEtaleRawEquiv A T N hA).trans
    (finiteExtEndpointEquiv (finiteEtaleConstantIso A T) (finiteEtaleLineIso A T N hA))

/-- The comparison image, with the constant source transported to pro-etale constants.
Source: diagonal trace finite coefficient comparison.
(blueprint: def-sfb-diagonal-trace-finite-etale-image). -/
@[irreducible] def finiteEtaleProImage (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0)
    (b : Ext (Etale.ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2) :
    Ext (geoCartierConstant A T) (geoCartierLine A N hA T) 2 :=
  finiteEtaleProEquiv A T N hA b

end AlgebraicGeometry.ProEtale.DiagonalTrace
