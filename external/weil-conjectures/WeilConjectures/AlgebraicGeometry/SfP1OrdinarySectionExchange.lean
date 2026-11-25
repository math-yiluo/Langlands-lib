/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.OrdinaryProperUnitInverseExchange
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits

/-! # Ordinary diagonal section exchange

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, exchange of the two
successive constant-object units (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  upperStar lowerStar ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteUnitPullback rightDerivedLowerShriek
  rightDerivedLowerShriekIsoRightDerivedLowerStar derivedTensorUnit

/-- The ordinary diagonal and projection units paste compatibly with inverse
proper exchange. Source: blueprint thm-amb-p1-adjunction.proof.md, the equation
`M = Rp2_* Delta_* M` and substitution of exchange counits
(auxiliary; not a blueprint node).

Proof: inverse constant-object base change for the diagonal replaces its unit,
the inverse coefficient comparison and inverse exchange by the self-product
coefficient inverse followed by pullback of the diagonal unit. Naturality of
projection exchange moves that pulled-back diagonal unit to the right. Inverse
constant-object base change for the projection replaces the remaining three
arrows by the coefficient inverse and pullback of the projection unit. Functoriality
then joins the two pulled-back units, which define projectiveLineDiagonalAlpha.
The calculation works for both projections and also for the empty base. -/
theorem ordinarySection_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (a : Bool) :
    supportedDerivedUnit A (projection f a) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          (supportedDerivedUnit A (TraceDiagonalDatum.diagonal f)) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
            (ordinaryFiniteUnitPullback A i.hom).inv) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          ((properExchange A (diagonalSquare f i hi)).inv.app
            (ordinaryFiniteUnit A (ProjectiveLine S))) ≫
        (properExchange A (projectionSquare f i hi a)).inv.app
          ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S))) =
      (ordinaryFiniteUnitPullback A i.hom).inv ≫
        (ordinaryFinitePullback A i.hom).map (projectiveLineDiagonalAlpha A S a) := by
  let R := ordinaryFinitePushforward A (projection f a)
  let D := ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)
  let Q := ordinaryFinitePullback A (productMap f i hi)
  let V := ordinaryFinitePullback A i.hom
  let T := ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)
  let v := ordinaryFiniteUnitPullback A i.hom
  let b := properExchange A (projectionSquare f i hi a)
  let δP := supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S))
  let CP := ordinaryFiniteUnit A (ProjectiveLine S)
  let CWP := ordinaryFiniteUnit A
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
  have hd' := constantUnit_inverseProperExchange A (diagonalSquare f i hi)
  have hp' := constantUnit_inverseProperExchange A (projectionSquare f i hi a)
  rw [projectiveLineDiagonalAlpha_units]
  rewrite [← R.map_comp_assoc (D.map v.inv), ← R.map_comp_assoc, hd', R.map_comp]
  simp only [Category.assoc]
  have hb : R.map (Q.map δP) ≫ b.inv.app
      ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj CP) =
      b.inv.app CWP ≫ V.map (T.map δP) := b.inv.naturality δP
  rewrite [hb, reassoc_of% hp']
  rw [← V.map_comp]

end AlgebraicGeometry.Etale.SfP1Transport
