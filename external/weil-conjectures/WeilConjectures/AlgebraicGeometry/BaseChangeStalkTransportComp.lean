/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.AlgebraicGeometry.BaseChangeTargetTransitionComp

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)

variable {Y : Scheme.{u}} {e : Y ⟶ T} {h : Y ⟶ X}

/-- Canonical target restriction commutes with transport from the original square.

Source: canonical pullback restrictions in Stacks Tags 0F07 and 09Z1.
(blueprint: lem-sbc-stalk-transport-composition)

Proof: expand the canonical pullback lifts and apply target transition composition.
Uniqueness of the lift identifies the composite of the two lifts with the direct lift.
The equation defining a morphism over T identifies the composite coefficient pullback
with the prescribed one. Apply the stalk functor and its composition law.
-/
theorem baseChangeStalkTransport_comp (sq : IsPullback e h g p)
    {U V : Over T} (φ : U ⟶ V) :
    baseChangeStalkTransport Λ p g q F x sq V ≫
      baseChangeTargetStalkMap Λ p g q F x φ =
        baseChangeStalkTransport Λ p g q F x sq U := by
  obtain ⟨TU, uU, πU⟩ := U
  obtain ⟨TV, uV, πV⟩ := V
  have hw := Over.w φ
  obtain ⟨f, r, w⟩ := φ
  change TU ⟶ TV at f
  change uU ⟶ uV at r
  change f ≫ πV = πU at hw
  subst πU
  let eV := pullback.fst (πV ≫ g) p
  let hV := pullback.snd (πV ≫ g) p
  let eU := pullback.fst ((f ≫ πV) ≫ g) p
  let hU := pullback.snd ((f ≫ πV) ≫ g) p
  let aV := sq.lift (eV ≫ πV) hV
    (by rw [Category.assoc]; exact pullback.condition)
  let aU := pullback.lift (eU ≫ f) hU
    (by
      calc
        (eU ≫ f) ≫ (πV ≫ g) = eU ≫ ((f ≫ πV) ≫ g) := by
          simp only [Category.assoc]
        _ = hU ≫ p := pullback.condition)
  have waV : aV ≫ e = eV ≫ πV := sq.lift_fst _ _ _
  have whV : aV ≫ h = hV := sq.lift_snd _ _ _
  have waU : aU ≫ eV = eU ≫ f := pullback.lift_fst _ _ _
  have whU : aU ≫ hV = hU := pullback.lift_snd _ _ _
  have ht := baseChangeTargetTransition_comp Λ e h q πV aV eV hV waV whV
    f aU eU hU waU whU F
  have ha : aU ≫ aV = sq.lift (eU ≫ (f ≫ πV)) hU
      ((Category.assoc eU (f ≫ πV) g).trans pullback.condition) := by
    apply sq.hom_ext
    · simp only [Category.assoc, waV, ← Category.assoc aU eV, waU,
        sq.lift_fst]
    · simp only [Category.assoc, whV, whU, sq.lift_snd]
  simp only [ha] at ht
  unfold baseChangeStalkTransport baseChangeTargetStalkMap
  rw [← Functor.map_comp]
  dsimp only [eV, hV, eU, hU, aV, aU] at ht
  apply congrArg ((X.uliftPointSmallEtale x).sheafFiber.map)
  exact ht

end AlgebraicGeometry.Etale
