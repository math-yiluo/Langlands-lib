/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import all WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionFamily

/-! # Compact-support action on a base where the automorphism is the identity

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/
sk-prop-sp-orientation/sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-compact-support-fixed-base-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek leftDerivedUpperStarComp
  leftDerivedUpperStarId derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor

private theorem fixed_identity_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (K : DerivedCategoryModule A X) :
    (affineLinearPullbackId A Y).inv.app _ ≫
      (rightDerivedLowerShriekBaseChangeMap A (IsPullback.id_horiz f)).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((affineLinearPullbackId A X).hom.app K) = 𝟙 _ := by
  have h := NatTrans.congr_app
    (unboundedEtaleCompactSupport_baseChange_id A f (IsPullback.id_horiz f)) K
  have h' := congrArg (fun z ↦
    (unboundedEtaleUpperStarIdIso A Y).inv.app _ ≫ z) h
  simpa [unboundedEtaleCompactSupportBaseChange, unboundedEtaleUpperStarIdIso,
    affineLinearPullbackId, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Iso.trans_hom, Iso.trans_inv, Category.assoc, Category.comp_id,
    Functor.map_comp, Iso.inv_hom_id_app_assoc] using h'

/-- An automorphism over `Y`, with coefficients pulled back from `Y`, acts trivially
on compact supports after a Cartesian base change on which it is the identity.

Source: vector-bundle orientation proof, Step 1, identity at the zero section
(blueprint: lem-pur-compact-support-fixed-base-action).
Proof: paste the automorphism square with the base-change square in both orders.
The inverse-image associativity law identifies the coefficient comparisons. The
base-changed automorphism and its coefficient comparison are the identity and the
pullback unitor. The identity exchange law makes its action the identity. Cancel
the invertible base-change and coefficient comparisons. No connectedness or trace
invariance is used.
-/
theorem compactSupport_fixed_base_action
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : X' ⟶ X} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback v f' f g) (a : X ⟶ X)
    (sa : IsPullback a f f (𝟙 Y)) (ha : a ≫ f = f)
    (hv : v ≫ a = v) (L : DerivedCategoryModule A Y) :
    (ordinaryFinitePullback A g).map
      ((affineLinearPullbackId A Y).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sa).app
          ((ordinaryFinitePullback A f).obj L) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a f f ha.symm).inv.app L)) =
      𝟙 _ := by
  let K := (ordinaryFinitePullback A f).obj L
  let K' := (ordinaryFinitePullback A f').obj ((ordinaryFinitePullback A g).obj L)
  let b := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app L
  let theta := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a f f ha.symm).inv.app L
  let theta' := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X') f' f'
    (Category.id_comp f').symm).inv.app ((ordinaryFinitePullback A g).obj L)
  have hw : (𝟙 X') ≫ v = v ≫ a := by rw [Category.id_comp, hv]
  have hb : (ordinaryFinitePullback A (𝟙 X')).map b.hom ≫ theta' =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hw)).inv.app K ≫
        (ordinaryFinitePullback A v).map theta ≫ b.hom := by
    exact descended_coefficient_square A f f' v g a (𝟙 X') sq.w ha
      (Category.id_comp f') hw L
  have h := affineLinearExchange_action_naturality A sq sa (IsPullback.id_horiz f')
    hw K K' theta theta' b.hom hb
  have ht : theta' = (affineLinearPullbackId A X').hom.app K' := by
    apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (𝟙 X') f' f' (Category.id_comp f').symm).hom.app
        ((ordinaryFinitePullback A g).obj L))).mp
    rw [pullback_id_eq]
    simpa only [theta', K', Iso.hom_inv_id_app, ordinaryFinitePullback] using
      (leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) f'
        ((ordinaryFinitePullback A g).obj L)).symm
  rw [ht, ← pullback_id_eq A Y'] at h
  have hid := fixed_identity_exchange A f' K'
  dsimp only [Functor.id_obj] at hid
  rw [hid] at h
  simp only [Category.comp_id] at h
  have hex := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let := hex
  apply (cancel_mono ((rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map b.hom)).mp
  simpa only [Category.assoc, Category.id_comp, K, theta, ← pullback_id_eq A Y] using h

end AlgebraicGeometry.Etale
