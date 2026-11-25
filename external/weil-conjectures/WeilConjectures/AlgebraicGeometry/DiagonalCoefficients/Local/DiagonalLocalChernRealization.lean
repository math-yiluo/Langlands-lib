/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints

/-! # Local Chern normalization and its actual derived adjunct -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The completed local class is fixed by the entire restricted Chern system.
Source: diagonal trace proof (1), coefficient and root-limit comparisons.
(blueprint: def-sfb-diagonal-local-chern-realization). -/
@[irreducible]
def ModelLocalChernNormalized (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧) : Prop :=
  (diagonalCompletedUnderlying l X).map z ≫
    DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
      (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
      (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
    p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
      p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map
        (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
          (Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S))))

/-- Realize an actual local completed arrow using the specified unit and line maps.
Source: diagonal coefficient changes (1).
(blueprint: def-sfb-diagonal-local-chern-realization). -/
@[irreducible]
def CompletedRealization.localChern (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X)
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧) :
    unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶
      ((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
          (zlLine l X))⟦(2 : ℤ)⟧ :=
  have : IsIso (e.singleUnit l X) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  inv (e.singleUnit l X) ≫ e.F.mapDerivedCategory.map z ≫ e.shiftedLine l X

/-- The canonical adjunct of a local class, transported to a specified derived model.
Source: diagonal coefficient changes (3), the normalized exchange mate.
(blueprint: def-sfb-diagonal-local-chern-realization). -/
@[irreducible]
def modelLocalAdjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (canonical : D.R = derivedLower Λ f) (cF : UnitPullEndpoint Λ f)
    {T : DerivedCategory (Modules Λ X)} (z : unit Λ X ⟶ T) :
    unit Λ S ⟶ D.R.obj T :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
      (cF.derived ≫ z) ≫ (eqToIso canonical).inv.app T

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
