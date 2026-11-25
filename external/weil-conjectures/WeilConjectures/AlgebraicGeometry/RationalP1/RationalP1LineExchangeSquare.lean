/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.RationalP1NativeTraceExchange
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The fixed projective-line coefficient square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.RationalP1

local instance instEssentiallySmallProfinite_rationalP1LineExchangeSquare
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

/-- The actual projective-line coefficient square, with fixed derived functors. -/
@[irreducible]
def LineExchangeSquare
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (cP : Endpoint (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
      (spRationalTwist (ProjectiveLine Y) l E) (spQbarTwist (ProjectiveLine Y) l)
      (closureLineMap l E (ProjectiveLine Y)))
    (cW : Endpoint (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
      (spRationalTwist (diagonalSurface Y) l E) (spQbarTwist (diagonalSurface Y) l)
      (closureLineMap l E (diagonalSurface Y))) : Prop :=
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
  let Λ := Profinite.continuousMapRingObj.{u} E.1
  let Λ' := Profinite.padicAlgClRingObj.{u} l
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let F' := moduleObjectDerivedPullback Λ' (ProjectiveLine Y ↘ Y)
  let R' := moduleObjectDerivedPushforward Λ' (ProjectiveLine Y ↘ Y)
  let S' := moduleObjectDerivedPushforward Λ' (secondProjection Y)
  let K := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (spRationalTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧
  let W := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
    (spRationalTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧
  let m := (derivedPushHom a (ProjectiveLine Y ↘ Y)).app K ≫ R'.map (cP.shift a)
  let n := (derivedPushHom a (secondProjection Y)).app W ≫ S'.map (cW.shift a)
  PullArrowSquare (F := F) (F' := F')
    (T := derivedScalars a Y) (U := derivedScalars a (ProjectiveLine Y))
    (derivedPullIso a (ProjectiveLine Y ↘ Y)) m
    (finiteSecondTraceExchange l E k p hpl Y)
    (closureSecondTraceExchange l k p hpl Y) n

end AlgebraicGeometry.ProEtale.RationalP1
