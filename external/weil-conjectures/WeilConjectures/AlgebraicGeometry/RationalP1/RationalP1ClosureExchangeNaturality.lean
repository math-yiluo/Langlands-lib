/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.RationalP1NativeModelExchange
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
local instance instEssentiallySmallProfinite_rationalP1ClosureExchangeNaturality
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
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

-- Identify the native coefficient presentation without unfolding derived resolutions.
/-- Extending coefficients commutes with the base-change operation on an arbitrary
adjunct from the coefficient unit to the direct image of the shifted root line.
There is no completed Chern class, normalization, trace equation, or prescribed
second adjunct in this statement. -/
theorem closure_exchange_naturality
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (d : Diagram (Profinite.continuousMapRingObj.{u} E.1) Y
      (fun X ↦ spRationalTwist X l E))
    (d' : Diagram (Profinite.padicAlgClRingObj.{u} l) Y (fun X ↦ spQbarTwist X l))
    (s : ScalarCompatibility (Profinite.padicSubfieldRingObjToPadicAlgCl l E) Y
      (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
      (closureLineMap l E) d d')
    (x : unit (coefficient l (some E)).X Y ⟶ d.Rq.R.obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l (some E)).X
        (ProjectiveLine Y)) 0).obj (line l (some E) (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) :
    let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
    let x' := extendScalarChern a (ProjectiveLine Y ↘ Y) (s.units Y) s.lineP
      d.Rq d'.Rq s.q.square x ≫ (eqToIso d'.q_canonical).hom.app _
    let z := (scalarUnitPullIso (coefficient l (some E)).X Y).inv ≫
      (moduleObjectDerivedPullback (coefficient l (some E)).X
        (ProjectiveLine Y ↘ Y)).map (x ≫ (eqToIso d.q_canonical).hom.app _) ≫
      secondTraceExchange l (some E) k p hpl Y ≫
      (secondDiagramPushIso _ Y _ d).inv.app _
    (moduleObjectDerivedPullback (coefficient l none).X
        (ProjectiveLine Y ↘ Y)).map x' ≫ secondTraceExchange l none k p hpl Y =
      (scalarUnitPullIso (coefficient l none).X Y).hom ≫
        extendScalarChern a (secondProjection Y) (s.units (ProjectiveLine Y)) s.lineW
          d.R₂ d'.R₂ s.p₂.square z ≫ (secondDiagramPushIso _ Y _ d').hom.app _ :=
  by
    have h := closure_exchange_naturality_native l E k p hpl Y d d' s x
    simp only [finiteSecondTraceExchange, closureSecondTraceExchange,
      secondDiagramPushIso, coefficient, line, Iso.app_hom, Iso.app_inv, id] at h ⊢
    coefficient_finish h

end AlgebraicGeometry.ProEtale.RationalP1
