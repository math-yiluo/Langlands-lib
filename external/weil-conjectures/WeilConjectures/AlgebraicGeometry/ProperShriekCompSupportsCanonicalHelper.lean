/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupportsRaw

/-! Canonical component normalization for the proper compact-support compositor. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/--
The inverse component of the canonical specified proper compositor is the inverse
component of the ordinary compact-support compositor.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node)
-/
theorem properRouteCompIso_inv_app_eq_canonical {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    [IsProper (p ≫ f)]
    (E : DerivedCategoryModule A W) :
    (properRouteCompIso A p f (p ≫ f) rfl).inv.app E =
      (rightDerivedLowerShriekCompIso A p f).inv.app E := by
  simp only [properRouteCompIso, rightDerivedLowerShriekCongrIso,
    Iso.trans_inv, Iso.symm_inv, Iso.refl_hom, Category.comp_id]

theorem properRouteCompIso_comp_app_eq_canonical {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    [IsProper (p ≫ f)]
    (E : DerivedCategoryModule A W) :
    (properRouteCompIso A p f (p ≫ f) rfl).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (p ≫ f)).hom.app E =
      (rightDerivedLowerShriekCompIso A p f).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (p ≫ f)).hom.app E := by
  rw [properRouteCompIso_inv_app_eq_canonical A p f E]

-- Compare the construction arguments explicitly, without reducing derived functors.
-- Every generated equality is checked by the kernel.
private meta def compositorCongr :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => throwError "compositor congruence exhausted: {a} versus {b}"
  | fuel + 1, a, b => do
    let a := (← Lean.instantiateMVars a).consumeMData
    let b := (← Lean.instantiateMVars b).consumeMData
    if a == b then return ← Lean.Meta.mkHEqRefl a
    if ← Lean.Meta.isProof a then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    let aa := a.getAppArgs
    let bb := b.getAppArgs
    let sameHead := a.getAppFn == b.getAppFn ||
      (a.getAppFn.constName?.isSome && a.getAppFn.constName? == b.getAppFn.constName?)
    unless sameHead && aa.size == bb.size && aa.size > 0 do
      throwError "compositor arguments differ: {a} versus {b}"
    let ct ← Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
    let mut pf := ct.proof
    for i in [:aa.size] do
      let ih ← compositorCongr fuel aa[i]! bb[i]!
      let arg ← match ct.argKinds[i]! with
        | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
        | .heq => pure ih
        | _ => throwError "unexpected compositor congruence argument"
      pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
    if (← Lean.Meta.inferType pf).isHEq then return pf
    return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]

/--
The raw proper forget-supports compositor remains valid when the properness
instance for the composite is made explicit. This is the raw calculation used
by the canonical-composite transport.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node)
-/
theorem properShriekComp_comp_forgetSupports_raw_with_comp {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    [IsProper (p ≫ f)] (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekCompIso A p f).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (p ≫ f)).hom.app E =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) p).hom.app E) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) f).hom.app
            ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  rename_i hp hf hpf
  cases Subsingleton.elim hpf (IsProper.instCompScheme p f)
  have h := properShriekComp_comp_forgetSupports_raw A p f E
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let some d := (← Lean.getLCtx).findFromUserName? `h
        | throwError "no raw compositor equation"
      let heq ← compositorCongr 100 target (← Lean.instantiateMVars d.type)
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[heq]
      let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
      (← Lean.Elab.Tactic.getMainGoal).assign pf

end AlgebraicGeometry.Etale
