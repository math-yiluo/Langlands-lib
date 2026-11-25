/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.RationalP1NativeTraceExchange
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.ScalarUnitPullNaturality
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.RationalP1NativeModelQEquation
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.RationalP1NativeModelP2Equation
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineExchangeAssembly
import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Coefficient naturality of the projective-line exchange
-/

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
attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedScalars

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward diagonalSurface secondProjection

set_option allowUnsafeReducibility true in
attribute [local irreducible] derivedPullIso derivedPushHom derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction
  firstProjection square upperStarFromPoint pullback limit
  DerivedCategory.monoidalClosed Mod.monoidalClosed CondensedRing.upperStar

-- Check the fixed derived model interfaces while keeping their resolutions folded.
/-- Assemble normalized-model scalar transport with the unit and line squares. -/
theorem closure_exchange_naturality_native
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (d : Diagram (Profinite.continuousMapRingObj.{u} E.1) Y
      (fun X ↦ spRationalTwist X l E))
    (d' : Diagram (Profinite.padicAlgClRingObj.{u} l) Y (fun X ↦ spQbarTwist X l))
    (s : ScalarCompatibility (Profinite.padicSubfieldRingObjToPadicAlgCl l E) Y
      (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
      (closureLineMap l E) d d')
    (x : unit (Profinite.continuousMapRingObj.{u} E.1) Y ⟶ d.Rq.R.obj
      (((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} E.1) (ProjectiveLine Y)) 0).obj
        (spRationalTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧)) :
    let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
    let Λ := Profinite.continuousMapRingObj.{u} E.1
    let Λ' := Profinite.padicAlgClRingObj.{u} l
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let F' := moduleObjectDerivedPullback Λ' (ProjectiveLine Y ↘ Y)
    let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (spRationalTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧
    let T' := ((DerivedCategory.singleFunctor (Modules Λ' (ProjectiveLine Y)) 0).obj
      (spQbarTwist (ProjectiveLine Y) l)) ⟦(2 : ℤ)⟧
    let W := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (spRationalTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧
    let W' := ((DerivedCategory.singleFunctor (Modules Λ' (diagonalSurface Y)) 0).obj
      (spQbarTwist (diagonalSurface Y) l)) ⟦(2 : ℤ)⟧
    F'.map (extendScalarChern a (ProjectiveLine Y ↘ Y) (s.units Y) s.lineP
        d.Rq d'.Rq s.q.square x ≫ ((eqToIso d'.q_canonical).app T').hom) ≫
      closureSecondTraceExchange l k p hpl Y =
    (scalarUnitPullIso Λ' Y).hom ≫
      extendScalarChern a (secondProjection Y) (s.units (ProjectiveLine Y)) s.lineW
        d.R₂ d'.R₂ s.p₂.square
        ((scalarUnitPullIso Λ Y).inv ≫
          F.map (x ≫ ((eqToIso d.q_canonical).app T).hom) ≫
            finiteSecondTraceExchange l E k p hpl Y ≫
              ((eqToIso d.p₂_canonical).app W).inv) ≫
        ((eqToIso d'.p₂_canonical).app W').hom := by
    intro a Λ Λ' F F' T T' W W'
    let m := (derivedPushHom a (ProjectiveLine Y ↘ Y)).app T ≫
      (moduleObjectDerivedPushforward Λ' (ProjectiveLine Y ↘ Y)).map (s.lineP.shift a)
    let n := (derivedPushHom a (secondProjection Y)).app W ≫
      (moduleObjectDerivedPushforward Λ' (secondProjection Y)).map (s.lineW.shift a)
    have hβ := rational_p1_line_exchange_assembly l E k p hpl Y s.lineP s.lineW
    unfold LineExchangeSquare at hβ
    dsimp only at hβ
    let z := (scalarUnitPullIso Λ Y).inv ≫
      F.map (x ≫ (eqToIso d.q_canonical).hom.app T) ≫
        finiteSecondTraceExchange l E k p hpl Y ≫
          (eqToIso d.p₂_canonical).inv.app W
    let e := extendScalarChern a (ProjectiveLine Y ↘ Y) (s.units Y) s.lineP
      d.Rq d'.Rq s.q.square x
    let e₂ := extendScalarChern a (secondProjection Y)
      (s.units (ProjectiveLine Y)) s.lineW d.R₂ d'.R₂ s.p₂.square z
    have hq₀ := native_q_model_equation l E Y d d' s x
    have h₂₀ := native_p2_model_equation l E Y d d' s z
    unfold PullArrowSquare at hβ
    have hβ₀ : (derivedPullIso a (ProjectiveLine Y ↘ Y)).hom.app
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj T) ≫
        F'.map m ≫ closureSecondTraceExchange l k p hpl Y =
        (derivedScalars a (ProjectiveLine Y)).map
          (finiteSecondTraceExchange l E k p hpl Y) ≫ n := by
      coefficient_finish hβ
    have hU₀ := scalar_unit_pull_naturality_explicit a Y
      (s.units Y) (s.units (ProjectiveLine Y))
    have h := coefficient_paste% [F, F', derivedScalars a Y,
      derivedScalars a (ProjectiveLine Y), derivedPullIso a (ProjectiveLine Y ↘ Y),
      (s.units Y).iso, (s.units (ProjectiveLine Y)).iso,
      scalarUnitPullIso Λ Y, scalarUnitPullIso Λ' Y,
      (eqToIso d.q_canonical).app T, (eqToIso d'.q_canonical).app T',
      (eqToIso d.p₂_canonical).app W, (eqToIso d'.p₂_canonical).app W',
      x, e, e₂, m, n, finiteSecondTraceExchange l E k p hpl Y,
      closureSecondTraceExchange l k p hpl Y, hU₀, hβ₀, hq₀, h₂₀]
    coefficient_finish h

end AlgebraicGeometry.ProEtale.RationalP1
