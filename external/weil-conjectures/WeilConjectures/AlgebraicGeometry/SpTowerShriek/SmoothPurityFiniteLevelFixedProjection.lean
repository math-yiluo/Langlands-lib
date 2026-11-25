/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-! # Finite-level projection: fixed origins -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Keep coefficient instances on the path used by the generic finite-ring theorem.
attribute [local instance 2000] CommRing.toRing

private def LevelGood (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) : Prop :=
  Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj K)} ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
    HasFiniteProEtaleTorAmplitude T A K

private theorem quotient_good (T : Scheme.{u})
    (I J : Ideal (Padic.coefficientExtensionIntegers l E)) (h : I = J)
    [Finite (Padic.coefficientExtensionIntegers l E ⧸ I)]
    [Finite (Padic.coefficientExtensionIntegers l E ⧸ J)]
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionIntegers l E ⧸ I))
    (hK : LevelGood T (Padic.coefficientExtensionIntegers l E ⧸ J)
      ((quotientTransport l E T I J h).obj K)) :
    LevelGood T (Padic.coefficientExtensionIntegers l E ⧸ I) K := by
  subst J
  exact hK

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor projectionMapOfCompactification

attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  SheafOfModules.OpenTensorNormalization.finiteTensor

private meta def projectionHeadAsApplication (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let f := e.getAppFn.consumeMData
  if let .proj n i v := f then
    let env ← Lean.getEnv
    let some info := Lean.getStructureInfo? env n | throwError "unknown structure {n}"
    let some p := Lean.getProjFnForField? env n (info.fieldNames[i]!) |
      throwError "unknown projection {n} {i}"
    let t ← Lean.Meta.whnfD (← Lean.Meta.inferType v)
    let .const _ us := t.getAppFn | throwError "projection has non-structure argument"
    let f := Lean.mkAppN (.const p us) (t.getAppArgs.push v)
    return Lean.mkAppN f e.getAppArgs
  return e

/- Factor coefficient-instance equalities at argument boundaries and cache them.
This is the proof-generating congruence used by FiniteIntrinsicProjectionCoordinates;
every generated equality is checked by Lean's kernel. -/
private meta def coefficientInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let entries ← cache.get
      if let some pf := entries[t]? then
        g.assign pf
        return
      for d in ← Lean.getLCtx do
        if (← Lean.instantiateMVars d.type).consumeMData == t then
          g.assign d.toExpr
          return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      let a := a.consumeMData
      let b := b.consumeMData
      for d in ← Lean.getLCtx do
        let dt := (← Lean.instantiateMVars d.type).consumeMData
        if let some (_, x, _, y) := dt.heq? then
          if t.isHEq && x.consumeMData == a && y.consumeMData == b then
            g.assign d.toExpr
            return
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else
        let a ← projectionHeadAsApplication a
        let b ← projectionHeadAsApplication b
        let common := a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0
        let a ← if common then pure a else
          projectionHeadAsApplication (← Lean.Meta.whnfD a)
        let b ← if common then pure b else
          projectionHeadAsApplication (← Lean.Meta.whnfD b)
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.isLambda && b.isLambda then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``Function.hfunext)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let mut pf := c.proof.beta #[f]
          for i in [:a.getAppNumArgs] do
            let k := c.argKinds[i + 1]!
            pf := Lean.mkApp pf a.getAppArgs[i]!
            unless k == .fixed do
              pf := Lean.mkApp pf b.getAppArgs[i]!
              if k == .eq || k == .heq then
                let ty ← Lean.Meta.whnfD (← Lean.Meta.inferType pf)
                unless ty.isForall do throwError "missing congruence equality binder"
                let h ← Lean.Meta.mkFreshExprMVar ty.bindingDomain!
                pf := Lean.mkApp pf h
                coefficientInstanceCongr cache fuel h.mvarId!
              else unless k == .subsingletonInst do
                throwError "unsupported congruence argument kind"
          g.assign pf
        else
          throwError "unsupported congruence at fuel {fuel}:\n{a}\nversus\n{b}"
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

end AlgebraicGeometry.ProEtale.SpTowerShriek
