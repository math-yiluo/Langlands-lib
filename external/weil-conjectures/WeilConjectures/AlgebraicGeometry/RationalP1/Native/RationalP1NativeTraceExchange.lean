/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Native endpoint types for the projective-line exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.RationalP1

local instance instEssentiallySmallProfinite_rationalP1NativeTraceExchange
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedPullIso derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction
  firstProjection secondProjection square upperStarFromPoint
  DerivedCategory.monoidalClosed Mod.monoidalClosed CondensedRing.upperStar

set_option allowUnsafeReducibility true in
attribute [local semireducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward

/-- The finite exchange, with its native coefficient and shifted-line endpoints. -/
@[irreducible]
def finiteSecondTraceExchange
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (moduleObjectDerivedPullback (Profinite.continuousMapRingObj.{u} E.1)
      (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward (Profinite.continuousMapRingObj.{u} E.1)
      (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor
          (Modules (Profinite.continuousMapRingObj.{u} E.1) (ProjectiveLine Y)) 0).obj
          (spRationalTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧)) ⟶
    (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj.{u} E.1)
      (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} E.1) (diagonalSurface Y)) 0).obj
        (spRationalTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧) :=
  secondTraceExchange l (some E) k p hpl Y

/-- The closure exchange, with its native coefficient and shifted-line endpoints. -/
@[irreducible]
def closureSecondTraceExchange
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (moduleObjectDerivedPullback (Profinite.padicAlgClRingObj.{u} l)
      (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj.{u} l)
      (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor
          (Modules (Profinite.padicAlgClRingObj.{u} l) (ProjectiveLine Y)) 0).obj
          (spQbarTwist (ProjectiveLine Y) l)) ⟦(2 : ℤ)⟧)) ⟶
    (moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj.{u} l)
      (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor
        (Modules (Profinite.padicAlgClRingObj.{u} l) (diagonalSurface Y)) 0).obj
        (spQbarTwist (diagonalSurface Y) l)) ⟦(2 : ℤ)⟧) :=
  secondTraceExchange l none k p hpl Y

end AlgebraicGeometry.ProEtale.RationalP1
