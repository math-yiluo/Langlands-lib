/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Factorization of the canonical coefficient base-change map

Source: Stacks Project, Tags 0097 and 08HY.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

-- Generate ordinary congruence proofs without unfolding functors at differing proof arguments.
-- Heterogeneous congruence lets proof irrelevance handle even different proposition types.
-- The resulting expression is checked by the kernel; this helper is used only for elaboration.
private def structuralEquality : Nat → Lean.Expr → Lean.Expr → Bool → Lean.Meta.MetaM Lean.Expr
  | 0, _, _, _ => throwError "Structural congruence exhausted its recursion bound"
  | fuel + 1, a, b, heterogeneous => do
    let a := a.consumeMData
    let b := b.consumeMData
    if a == b then
      if heterogeneous then return ← Lean.Meta.mkHEqRefl a else return ← Lean.Meta.mkEqRefl a
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      let p ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if heterogeneous then return p else return ← Lean.Meta.mkEqOfHEq p
    if a.isApp && b.isApp && a.getAppFn == b.getAppFn &&
        a.getAppArgs.size == b.getAppArgs.size then
      let ct ← Lean.Meta.mkHCongrWithArity a.getAppFn a.getAppArgs.size
      let mut args := #[]
      for i in [:a.getAppArgs.size] do
        let x := a.getAppArgs[i]!
        let y := b.getAppArgs[i]!
        let p ← structuralEquality fuel x y (ct.argKinds[i]! == .heq)
        args := args ++ #[x, y, p]
      let p := Lean.mkAppN ct.proof args
      if heterogeneous then return p else return ← Lean.Meta.mkEqOfHEq p
    throwError "Structural mismatch: {a.getAppFn.constName?}, {b.getAppFn.constName?}"

/-- Canonical base change postcomposes the square mate with the coefficient comparison.
Source: Stacks Project, Tag 08HY, base-change construction; Tag 0097, composition.
(blueprint: lem-sc-picard-base-change-factorization)

Proof: Substitute the assumed equality for I. The hom of a composite isomorphism is
its two homs composed. The first is the tensor-pullback composition comparison;
the second transports along v q_W = q_T, proved by the first projection identity
of the pullback lift defining v. These are exactly the coefficient morphism in
picardDirectImageBaseChangeMap. Its preceding factor is moduleBaseChangeMap for
the square v p_W = p_T h. Proof irrelevance identifies the proofs of these two
projection equations with the proofs in the canonical map's definition. This
proves the factorization. The argument does not use a counit, conjugation, a
cartesian-square isomorphism criterion, or nonzero coefficients, and applies to
empty schemes and zero modules as well. -/
theorem picardDirectImageBaseChangeMap_factorization
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules)
    (I : (tensorPullback (picardBaseChangeTop f j h)).obj
        ((tensorPullback (Limits.pullback.fst f j)).obj M) ≅
      (tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M)
    (hI : I = (picardTensorCompIso (picardBaseChangeTop f j h)
        (Limits.pullback.fst f j) M ≪≫
      eqToIso (congrArg (fun k ↦ (tensorPullback k).obj M)
        (show picardBaseChangeTop f j h ≫ Limits.pullback.fst f j =
            Limits.pullback.fst f (h ≫ j) from by
          dsimp [picardBaseChangeTop]
          rw [Limits.pullback.lift_fst])))) :
    picardDirectImageBaseChangeMap f j h M =
      moduleBaseChangeMap (Limits.pullback.snd f j)
        (Limits.pullback.snd f (h ≫ j)) h (picardBaseChangeTop f j h)
        (by dsimp [picardBaseChangeTop]; rw [Limits.pullback.lift_snd])
        ((tensorPullback (Limits.pullback.fst f j)).obj M) ≫
      (pushforward (Limits.pullback.snd f (h ≫ j))).map I.hom := by
  have ht := congrArg (fun J :
      (tensorPullback (picardBaseChangeTop f j h)).obj
        ((tensorPullback (Limits.pullback.fst f j)).obj M) ≅
      (tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M ↦ J.hom) hI
  simp only [Iso.trans_hom] at ht
  have hp := congrArg ((pushforward (Limits.pullback.snd f (h ≫ j))).map) ht
  have hb := congrArg (fun a ↦
    moduleBaseChangeMap (Limits.pullback.snd f j)
      (Limits.pullback.snd f (h ≫ j)) h (picardBaseChangeTop f j h)
      (by dsimp [picardBaseChangeTop]; rw [Limits.pullback.lift_snd])
      ((tensorPullback (Limits.pullback.fst f j)).obj M) ≫ a) hp.symm
  dsimp only [picardDirectImageBaseChangeMap]
  -- The two composites differ only in synthesized pullback-instance and equation proofs.
  -- Build explicit congruences instead of asking definitional equality to unfold their types.
  run_tac Lean.Elab.Tactic.withMainContext do
    let hb ← Lean.Meta.getLocalDeclFromUserName `hb
    let tgt := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
    let hbt := (← Lean.instantiateMVars hb.type).consumeMData
    let lhs ← structuralEquality 100 tgt.getAppArgs[1]! hbt.getAppArgs[1]! false
    let rhs ← structuralEquality 100 hbt.getAppArgs[2]! tgt.getAppArgs[2]! false
    let p ← Lean.Meta.mkEqTrans (← Lean.Meta.mkEqTrans lhs (Lean.mkFVar hb.fvarId)) rhs
    (← Lean.Elab.Tactic.getMainGoal).assign p
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.Scheme.Modules
