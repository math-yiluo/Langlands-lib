/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.CategoryTheory.Adjunction.ProperOpenTransport

/-!
# Components of the strict proper/open comparison

The strict-tower proper/open comparison alpha is, componentwise, the abstract comparison
`ProperOpenTransport.alphaApp` of its adjunction data.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8 (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

theorem openToR_eq_openToPush {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    letI := jAdj_unit_isIso B j
    openToR B j = ProperOpenTransport.openToPush (jAdj B j) (adj B j) := by
  ext M
  simp [openToR, ProperOpenTransport.openToPush]

instance openToPush_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] :
    letI := jAdj_unit_isIso B j
    IsIso (ProperOpenTransport.openToPush (jAdj B j) (adj B j)) := by
  have := openToR_isIso B j
  rw [← openToR_eq_openToPush]
  infer_instance

theorem betaInvApp_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) (M : Derived B U) :
    IsIso (ProperOpenTransport.betaInvApp (jAdj B j) (jAdj B j') (squareG B gU j' j g h) M) := by
  have := betaInv_isIso B gU j' j g h hsq
  exact (inferInstance : IsIso ((betaInv B gU j' j g h).app M))

theorem beta_hom_app {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) (M : Derived B U) :
    haveI := betaInvApp_isIso B gU j' j g h hsq M
    (beta B gU j' j g h hsq).hom.app M =
      inv (ProperOpenTransport.betaInvApp (jAdj B j) (jAdj B j') (squareG B gU j' j g h) M) := by
  have := betaInv_isIso B gU j' j g h hsq
  have := betaInvApp_isIso B gU j' j g h hsq M
  change (inv (betaInv B gU j' j g h)).app M = _
  rw [NatIso.isIso_inv_app]
  congr 1

theorem pi_eq_clopenProjection {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] :
    letI := jAdj_unit_isIso B s
    pi B s = ProperOpenTransport.clopenProjection (jAdj B s) (adj B s) := by
  have := openToR_isIso B s
  unfold pi ProperOpenTransport.clopenProjection
  congr 2
  exact IsIso.inv_eq_inv.mpr (openToR_eq_openToPush B s)

/-- The strict proper/open comparison is the abstract one of its adjunction data. -/
theorem alpha_eq_absAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    alpha B k r p i h = ProperOpenTransport.absAlpha
      (beta B (pullback.snd p i) (pullback.fst p i) i p
        (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip)
      (pi B (squareLift k r p i h))
      (jComp B (squareLift k r p i h) (pullback.fst p i)) (jCongr B (pullback.lift_fst k r h))
      (gComp B (squareLift k r p i h) (pullback.snd p i))
      (eqToIso (congrArg (G B) (pullback.lift_snd k r h))) := rfl

/-- The strict proper/open gamma is the proper-adjunction mate of alpha. -/
theorem gamma_eq_mateEquiv {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    gamma B k r p i h = mateEquiv (adj B r) (adj B p) (alpha B k r p i h) := rfl

/-- The strict proper/open comparison, componentwise, is the abstract one. -/
theorem alpha_app_eq_alphaApp {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    [IsIso (jAdj B (squareLift k r p i h)).unit]
    [IsIso (ProperOpenTransport.openToPush (jAdj B (squareLift k r p i h))
      (adj B (squareLift k r p i h)))]
    [∀ x, IsIso (ProperOpenTransport.betaInvApp (jAdj B i) (jAdj B (pullback.fst p i))
      (squareG B (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm) x)]
    (x : Derived B S) :
    (alpha B k r p i h).app x = ProperOpenTransport.alphaApp
      (jAdj B i) (jAdj B (pullback.fst p i)) (jAdj B (squareLift k r p i h))
      (adj B (squareLift k r p i h))
      (squareG B (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm)
      (jComp B (squareLift k r p i h) (pullback.fst p i) ≪≫ jCongr B (pullback.lift_fst k r h))
      ((gComp B (squareLift k r p i h) (pullback.snd p i)).symm ≪≫
        eqToIso (congrArg (G B) (pullback.lift_snd k r h))) x := by
  rw [alpha_eq_absAlpha]
  refine ProperOpenTransport.absAlpha_app_eq_alphaApp_of_eq _ _ _ _ _ _ (fun x ↦ ?_) _
    (pi_eq_clopenProjection B _) _ _ _ _ x
  rw [beta_hom_app]

end AlgebraicGeometry.ProEtale.StrictTower
