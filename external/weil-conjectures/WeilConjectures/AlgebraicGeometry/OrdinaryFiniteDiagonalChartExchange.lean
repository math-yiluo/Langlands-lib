/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistComposition

/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Exchange for the two normalized projective-line diagonal charts -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3
attribute [local instance 100000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  AlgebraicGeometry.ProjectiveSpace derivedUpperStarLowerStarAdjunction
  rightDerivedLowerStarComp rightDerivedLowerStarCongr
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

/-- The self square with the selected projection as its vertical arrow. -/
theorem projectiveLineDiagonalSquare (S : Scheme.{u}) (a : Bool) :
    CommSq (projectiveLineDiagonalProjection S (!a))
      (projectiveLineDiagonalProjection S a) (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) :=
  match a with
  | false => (IsPullback.of_hasPullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).flip.toCommSq
  | true => (IsPullback.of_hasPullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).toCommSq

/-- The unselected coordinate of the diagonal chart is the standard projective-line map. -/
theorem projectiveLineDiagonalChart_other (S : Scheme.{u}) (a : Bool) :
    (projectiveLineDiagonalChart S a).val.hom ≫ projectiveLineDiagonalProjection S (!a) =
      ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S) := by
  cases a
  · exact (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2))
      (ProjectiveLine S ↘ S)).flip.isoPullback_hom_snd
  · exact (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2))
      (ProjectiveLine S ↘ S)).isoPullback_hom_fst

private theorem pullback_natCast_isUnit (N : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsUnit (N : Γ(Y, ⊤))) : IsUnit (N : Γ(X, ⊤)) := by
  simpa only [map_natCast] using h.map f.appTop.hom

private theorem invert_composite {C : Type*} [Category C]
    {X Y Z : C} (e : X ≅ Y) (a : Y ⟶ Z) (b : X ⟶ Z) (h : e.hom ≫ a = b) :
    a = e.inv ≫ b := by
  rw [← h, Iso.inv_hom_id_assoc]

/-- The chart map after self exchange is standard projective-line exchange. -/
theorem ordinaryFiniteDiagonalChart_exchange
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) (projectiveLineDiagonalSquare S a)).app
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (projectiveLineDiagonalProjection S (!a)) (affineTraceProjectiveInvertible N S hS)).hom ≫
      ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
    (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S)).toCommSq).app
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S))
          (affineTraceProjectiveInvertible N S hS)).hom := by
  let e := (projectiveLineDiagonalChart S a).val.hom
  let p := projectiveLineDiagonalProjection S a
  let r := projectiveLineDiagonalProjection S (!a)
  let q' := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let m := ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S)
  let hP := affineTraceProjectiveInvertible N S hS
  let hW := pullback_natCast_isUnit N
    ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
      (ProjectiveLine S ↘ S)) hS
  have hp : q' = e ≫ p := (projectiveLineDiagonalChart S a).property.symm
  have hm : m = e ≫ r := (projectiveLineDiagonalChart_other S a).symm
  have hc := ordinaryFiniteShiftedLinePullback_comp_of_eq A N hN hA t e r m hm hP hW
  have hc' : (ordinaryFinitePullback A e).map
        (ordinaryFiniteShiftedLinePullback A N hA t r hP).hom ≫
        (ordinaryFiniteShiftedLinePullback A N hA t e hW).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e r m hm).inv.app
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFiniteShiftedLinePullback A N hA t m hP).hom :=
    invert_composite
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e r m hm).app
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) _ _ hc
  have hh := derivedBaseChangeMap_chart_coefficient_cached (ModuleCat.{u + 1} A)
    (projectiveLineDiagonalSquare S a) e q' hp m hm
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S)).toCommSq
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hA (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (ordinaryFiniteShiftedLinePullback A N hA t r hP).hom
    (ordinaryFiniteShiftedLinePullback A N hA t e hW).hom
    (ordinaryFiniteShiftedLinePullback A N hA t m hP).hom hc'
  exact (congrArg (fun z ↦
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) (projectiveLineDiagonalSquare S a)).app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A p).map
        (ordinaryFiniteShiftedLinePullback A N hA t r hP).hom ≫ z)
    (ordinaryFiniteDiagonalChartMap_eq_generic A N hA t S hS a)).trans hh

end AlgebraicGeometry.Etale
