/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection

/-! # Finite integral coordinates for a strict Chern arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Insert integral constants into the actual finite coefficient sheaf, evaluate a
strict-system arrow, and project its line endpoint to finite roots. All data are
specified maps: this construction uses no normalization equation or chosen lift.
Source: diagonal tower trace proof (1), finite coefficient and root coordinates.
(blueprint: def-diagonal-local-finite-cone-chern-class). -/
@[irreducible]
def finiteConeChernClass
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (theta : unit T (Arings l (ULift.{u} (Padic l)) T) ⟶
      (line l (ULift.{u} (Padic l)) c)⟦(2 : ℤ)⟧) :
    Ext.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((cartierForget A T).obj
        (geoCartierLine A (l ^ (n + 1)) hA T)) 2 :=
  Ext.homEquiv.symm
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
      (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n)) ≫
      mapSingleArrow
        (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙ diagonalForget l T)
        (2 : ℤ) theta ≫
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (k.lineForget.hom.app (op n) ≫
          cartierProRootMap A (l ^ (n + 1)) hA T
            (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧')

end AlgebraicGeometry.ProEtale.DiagonalTrace
