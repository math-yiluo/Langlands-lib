/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.CategoryTheory.Adjunction.ProperOpenTransport

/-!
# Components of the completed proper/open comparison

The completed proper/open comparison `cbcProperOpenAlpha` is the abstract comparison
`ProperOpenTransport.absAlpha` of its adjunction data, with the abstract clopen projection
and open base-change transpose.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8 (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The completed proper/open comparison is the abstract one of its adjunction data. -/
theorem cbcProperOpenAlpha_eq_absAlpha {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    cbcProperOpenAlpha d k r p i h = ProperOpenTransport.absAlpha
      (cbcBeta d (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip)
      (cbcClopenProjection d (ProEtale.StrictTower.squareLift k r p i h))
      (cbcJComp d (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i))
      (cbcJCongr d (pullback.lift_fst k r h))
      (d.pullComp (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i))
      (eqToIso (congrArg (fun f ↦ d.pull f) (pullback.lift_snd k r h))) := rfl

theorem cbcOpenToPush_eq_openToPush {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    letI := cbcOpenUnit_isIso d j
    cbcOpenToPush d j = ProperOpenTransport.openToPush (cbcDerivedOpenAdjunction d j)
      (cbcPullPushAdjunction d j) := by
  ext M
  simp [cbcOpenToPush, ProperOpenTransport.openToPush]

theorem cbcOpenToPush_abstract_isIso {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    [IsClosedImmersion j] :
    letI := cbcOpenUnit_isIso d j
    IsIso (ProperOpenTransport.openToPush (cbcDerivedOpenAdjunction d j)
      (cbcPullPushAdjunction d j)) := by
  have := cbcOpenToPush_isIso d j
  rw [← cbcOpenToPush_eq_openToPush]
  infer_instance

theorem cbcClopenProjection_eq {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    [IsClosedImmersion j] :
    letI := cbcOpenUnit_isIso d j
    letI := cbcOpenToPush_abstract_isIso d j
    cbcClopenProjection d j = ProperOpenTransport.clopenProjection
      (cbcDerivedOpenAdjunction d j) (cbcPullPushAdjunction d j) := by
  have := cbcOpenToPush_abstract_isIso d j
  have := cbcOpenToPush_isIso d j
  unfold cbcClopenProjection ProperOpenTransport.clopenProjection
  congr 2
  exact IsIso.inv_eq_inv.mpr (cbcOpenToPush_eq_openToPush d j)

theorem cbcBetaInv_eq_betaInvNat {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) :
    cbcBetaInv d a j' j g h =
      ProperOpenTransport.betaInvNat (cbcDerivedOpenAdjunction d j)
        (cbcDerivedOpenAdjunction d j') (cbcSquarePull d a j' j g h) := rfl

theorem cbcBetaInvNat_isIso {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    IsIso (ProperOpenTransport.betaInvNat (cbcDerivedOpenAdjunction d j)
        (cbcDerivedOpenAdjunction d j') (cbcSquarePull d a j' j g h)) := by
  rw [← cbcBetaInv_eq_betaInvNat]
  exact cbcBetaInv_isIso d a j' j g h sq

theorem cbcBeta_hom {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    haveI := cbcBetaInvNat_isIso d a j' j g h sq
    (cbcBeta d a j' j g h sq).hom =
      inv (ProperOpenTransport.betaInvNat (cbcDerivedOpenAdjunction d j)
        (cbcDerivedOpenAdjunction d j') (cbcSquarePull d a j' j g h)) := by
  have := cbcBetaInv_isIso d a j' j g h sq
  have := cbcBetaInvNat_isIso d a j' j g h sq
  change inv (cbcBetaInv d a j' j g h) = _
  exact IsIso.inv_eq_inv.mpr (cbcBetaInv_eq_betaInvNat d a j' j g h)

/-- The completed proper/open gamma is the proper-adjunction mate of alpha. -/
theorem cbcProperOpenGamma_eq_mateEquiv {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    cbcProperOpenGamma d k r p i h = mateEquiv (cbcPullPushAdjunction d r)
      (cbcPullPushAdjunction d p) (cbcProperOpenAlpha d k r p i h) := rfl

/-- The completed proper/open comparison, componentwise, is the abstract one. -/
theorem cbcProperOpenAlpha_app_eq_alphaApp {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    [IsIso (cbcDerivedOpenAdjunction d (ProEtale.StrictTower.squareLift k r p i h)).unit]
    [IsIso (ProperOpenTransport.openToPush
      (cbcDerivedOpenAdjunction d (ProEtale.StrictTower.squareLift k r p i h))
      (cbcPullPushAdjunction d (ProEtale.StrictTower.squareLift k r p i h)))]
    [∀ x, IsIso (ProperOpenTransport.betaInvApp (cbcDerivedOpenAdjunction d i)
      (cbcDerivedOpenAdjunction d (pullback.fst p i))
      (cbcSquarePull d (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm) x)]
    (x : d.derived S) :
    (cbcProperOpenAlpha d k r p i h).app x = ProperOpenTransport.alphaApp
      (cbcDerivedOpenAdjunction d i) (cbcDerivedOpenAdjunction d (pullback.fst p i))
      (cbcDerivedOpenAdjunction d (ProEtale.StrictTower.squareLift k r p i h))
      (cbcPullPushAdjunction d (ProEtale.StrictTower.squareLift k r p i h))
      (cbcSquarePull d (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm)
      (cbcJComp d (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i) ≪≫
        cbcJCongr d (pullback.lift_fst k r h))
      ((d.pullComp (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i)).symm ≪≫
        eqToIso (congrArg (fun f ↦ d.pull f) (pullback.lift_snd k r h))) x := by
  -- `refine` takes all the data from the goal, so that the kernel never compares
  -- differently elaborated components of a concrete natural transformation.
  rw [cbcProperOpenAlpha_eq_absAlpha]
  refine ProperOpenTransport.absAlpha_app_eq_alphaApp_of_eq _ _ _ _ _ _ ?_ _ ?_ _ _ _ _ _
  · intro y
    have := cbcBetaInvNat_isIso d (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip
    rw [cbcBeta_hom, ProperOpenTransport.inv_betaInvNat_app]
  · have := cbcOpenToPush_isIso d (ProEtale.StrictTower.squareLift k r p i h)
    exact cbcClopenProjection_eq d (ProEtale.StrictTower.squareLift k r p i h)

end AlgebraicGeometry.Scheme
