/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.AlgebraicGeometry.RationalP1.NormalizedScalarChernModel
import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange

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
local instance instEssentiallySmallProfinite_rationalP1NativeModelQEquation
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

/-- Scalar transport through the first native normalized model. -/
theorem native_q_model_equation
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
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
    let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (spRationalTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧
    let T' := ((DerivedCategory.singleFunctor (Modules Λ' (ProjectiveLine Y)) 0).obj
      (spQbarTwist (ProjectiveLine Y) l)) ⟦(2 : ℤ)⟧
    extendScalarChern a (ProjectiveLine Y ↘ Y) (s.units Y) s.lineP
        d.Rq d'.Rq s.q.square x ≫ (eqToIso d'.q_canonical).hom.app T' =
      (s.units Y).iso.inv ≫ (derivedScalars a Y).map
        (x ≫ (eqToIso d.q_canonical).hom.app T) ≫
        (derivedPushHom a (ProjectiveLine Y ↘ Y)).app T ≫
          (moduleObjectDerivedPushforward Λ' (ProjectiveLine Y ↘ Y)).map (s.lineP.shift a) := by
  have h := extendScalarChern_canonical
    (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E)
    (ProjectiveLine Y ↘ Y) (s.units Y) s.lineP d.Rq d'.Rq
    d.q_canonical d'.q_canonical d.q_unit d'.q_unit s.q.square x
  coefficient_finish h

end AlgebraicGeometry.ProEtale.RationalP1
