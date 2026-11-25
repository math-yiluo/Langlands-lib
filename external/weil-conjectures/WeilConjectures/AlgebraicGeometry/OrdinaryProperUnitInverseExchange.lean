/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantBaseChange

/-! # Inverse transport of constant-object units

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, exchange of canonical
pullback units (auxiliary; not a blueprint node).
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

private theorem constantUnit_properExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y Y' Z Z' : Scheme.{u}}
    {g : Y ⟶ Z} {g' : Y' ⟶ Z'} {v : Y' ⟶ Y} {w : Z' ⟶ Z}
    [IsProper g] (sq : IsPullback v g' g w) :
    (ordinaryFinitePullback A w).map (supportedDerivedUnit A g) ≫
        (properExchange A sq).hom.app (ordinaryFiniteUnit A Y) ≫
        (ordinaryFinitePushforward A g').map (ordinaryFiniteUnitPullback A v).hom =
      (ordinaryFiniteUnitPullback A w).hom ≫ supportedDerivedUnit A g' := by
  simpa only [properExchange, asIso_hom, ordinaryFinitePullback, ordinaryFinitePushforward] using
    ordinaryFiniteConstant_baseChange A sq.toCommSq

private theorem inverse_comparison
    {C : Type*} [Category C] {P Q R S : C}
    (a : P ⟶ Q) (d : R ⟶ S) (q : P ≅ R) (v : Q ≅ S)
    (h : a ≫ v.hom = q.hom ≫ d) : d ≫ v.inv = q.inv ≫ a := by
  have h' := congrArg (fun k ↦ q.inv ≫ k ≫ v.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using h'.symm

/-- Invertible proper exchange transports the two constant-object units in the
inverse direction. Source: blueprint thm-amb-p1-adjunction.proof.md, substitution
of the pullback counits (auxiliary; not a blueprint node).

Proof: ordinary constant-object base change gives the forward square. Compose
its exchange component with direct image of the constant pullback isomorphism.
This composite is invertible. Cancel it on the right and the constant pullback
comparison on the left. The inverse of the composite is direct image of the
inverse constant comparison followed by inverse exchange, which gives the
formula. This uses no projective-line geometry or nonemptiness hypothesis. -/
theorem constantUnit_inverseProperExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y Y' Z Z' : Scheme.{u}}
    {g : Y ⟶ Z} {g' : Y' ⟶ Z'} {v : Y' ⟶ Y} {w : Z' ⟶ Z}
    [IsProper g] (sq : IsPullback v g' g w) :
    supportedDerivedUnit A g' ≫
        (ordinaryFinitePushforward A g').map (ordinaryFiniteUnitPullback A v).inv ≫
        (properExchange A sq).inv.app (ordinaryFiniteUnit A Y) =
      (ordinaryFiniteUnitPullback A w).inv ≫
        (ordinaryFinitePullback A w).map (supportedDerivedUnit A g) := by
  have he : (ordinaryFinitePullback A w).map (supportedDerivedUnit A g) ≫
      (((properExchange A sq).app (ordinaryFiniteUnit A Y)) ≪≫
        (ordinaryFinitePushforward A g').mapIso (ordinaryFiniteUnitPullback A v)).hom =
      (ordinaryFiniteUnitPullback A w).hom ≫ supportedDerivedUnit A g' := by
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
      constantUnit_properExchange A sq
  simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using
    inverse_comparison
      ((ordinaryFinitePullback A w).map (supportedDerivedUnit A g))
      (supportedDerivedUnit A g') (ordinaryFiniteUnitPullback A w)
      (((properExchange A sq).app (ordinaryFiniteUnit A Y)) ≪≫
        (ordinaryFinitePushforward A g').mapIso (ordinaryFiniteUnitPullback A v)) he

end AlgebraicGeometry.Etale.SfP1Transport
