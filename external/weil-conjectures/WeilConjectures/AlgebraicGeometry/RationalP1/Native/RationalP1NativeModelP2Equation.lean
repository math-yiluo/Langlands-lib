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
local instance instEssentiallySmallProfinite_rationalP1NativeModelP2Equation
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

/-- Scalar transport through the second native normalized model, for any input z. -/
theorem native_p2_model_equation
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    (d : Diagram (Profinite.continuousMapRingObj.{u} E.1) Y
      (fun X ↦ spRationalTwist X l E))
    (d' : Diagram (Profinite.padicAlgClRingObj.{u} l) Y (fun X ↦ spQbarTwist X l))
    (s : ScalarCompatibility (Profinite.padicSubfieldRingObjToPadicAlgCl l E) Y
      (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
      (closureLineMap l E) d d')
    (z : unit (Profinite.continuousMapRingObj.{u} E.1) (ProjectiveLine Y) ⟶ d.R₂.R.obj
      (((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} E.1) (diagonalSurface Y)) 0).obj
        (spRationalTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧)) :
    let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
    let Λ := Profinite.continuousMapRingObj.{u} E.1
    let Λ' := Profinite.padicAlgClRingObj.{u} l
    let W := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (spRationalTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧
    let W' := ((DerivedCategory.singleFunctor (Modules Λ' (diagonalSurface Y)) 0).obj
      (spQbarTwist (diagonalSurface Y) l)) ⟦(2 : ℤ)⟧
    extendScalarChern a (secondProjection Y) (s.units (ProjectiveLine Y)) s.lineW
        d.R₂ d'.R₂ s.p₂.square z ≫ (eqToIso d'.p₂_canonical).hom.app W' =
      (s.units (ProjectiveLine Y)).iso.inv ≫
        (derivedScalars a (ProjectiveLine Y)).map
          (z ≫ (eqToIso d.p₂_canonical).hom.app W) ≫
        (derivedPushHom a (secondProjection Y)).app W ≫
          (moduleObjectDerivedPushforward Λ' (secondProjection Y)).map (s.lineW.shift a) := by
  have h := extendScalarChern_canonical
    (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E)
    (secondProjection Y) (s.units (ProjectiveLine Y)) s.lineW d.R₂ d'.R₂
    d.p₂_canonical d'.p₂_canonical d.p₂_unit d'.p₂_unit s.p₂.square z
  coefficient_finish h

end AlgebraicGeometry.ProEtale.RationalP1
