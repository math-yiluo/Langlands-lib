/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import Mathlib.Lean.Meta.CongrTheorems
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteProperProjectionWord
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteOpenProjectionTail

/-! Compatibility of the normalized finite tensor with the projection word. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

section CoefficientCoordinates

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory HasDerivedCategory.standard derivedTensor
  rightDerivedLowerStarProjectionMap derivedOpenImmersionLowerShriekProjectionIso
  leftDerivedUpperStarCompactificationIso projectionMapOfCompactification

end CoefficientCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] comparisonFinitePull comparisonFiniteOpen
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  sfIntrinsicModuleEquivalence derivedTensor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
  rightDerivedLowerStarProjectionMap derivedOpenImmersionLowerShriekProjectionIso
  leftDerivedUpperStarCompactificationIso projectionMapOfCompactification
  comparisonFiniteF comparisonLevelProjection

-- Canonical class diamonds are equal before substituting the finite quotient ring.
private theorem coefficient_ulift_ring (A : Type u) [CommRing A] :
    (ULift.ring : Ring (ULift.{u + 1, u} A)) = ULift.commRing.toRing := by
  rfl

private theorem coefficient_braided (A : Type u) [CommRing A] :
    (ModuleCat.MonoidalCategory.instBraidedCategory : BraidedCategory (ModuleCat.{u} A)) =
      ModuleCat.MonoidalCategory.symmetricCategory.toBraidedCategory := by
  rfl

-- Adapted from SmoothPurityFiniteLevelFixedProjection and
-- TowerCompactSupportProjectionFormulaIsos: cache ordinary heterogeneous
-- congruence proofs at coefficient-instance argument boundaries.
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

-- Expose composition and tensor wrappers before comparing their dependent arguments.
private meta def projectionNormalizeHead (fuel : Nat) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e ← projectionHeadAsApplication e.consumeMData
    let names := [``comparisonFiniteProjection, ``finiteF,
      ``SheafOfModules.OpenTensorNormalization.FiniteD,
      ``SheafOfModules.OpenTensorNormalization.FiniteModules,
      ``SheafOfModules.OpenTensorNormalization.finiteTensor,
      ``rightDerivedLowerShriekOfCompactification,
      ``derivedTensorRightDerivedLowerShriek,
      ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      ``CategoryTheory.Functor.uncurry, ``CategoryTheory.Functor.comp,
      ``CategoryTheory.Functor.postcompose₂, ``CategoryTheory.Functor.whiskeringLeft₂,
      ``CategoryTheory.Functor.whiskeringLeft, ``CategoryTheory.Functor.whiskeringRight,
      ``CategoryTheory.Functor.id, ``id]
    if names.any e.getAppFn.isConstOf then
      if let some e' ← Lean.Meta.unfoldDefinition? e then
        return ← projectionNormalizeHead fuel e'
    let args := e.getAppArgs
    let offset? := if e.getAppFn.isConstOf ``CategoryTheory.Functor.obj && args.size ≥ 2
      then some 2 else if e.getAppFn.isConstOf ``CategoryTheory.Functor.map && args.size ≥ 4
      then some 4 else none
    if let some offset := offset? then
      let i := args.size - offset
      let F' ← projectionNormalizeHead fuel args[i]!
      if F' != args[i]! then
        let e' := Lean.mkAppN e.getAppFn (args.set! i F')
        return ← projectionNormalizeHead fuel
          (← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e'))
    let e' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e)
    let e' ← projectionHeadAsApplication e'
    if e' != e then return ← projectionNormalizeHead fuel e'
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
        let ctx ← Lean.getLCtx
        let missing := pf.find? fun e => match e with
          | .fvar id => !(ctx.contains id)
          | _ => false
        if missing.isNone then
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
        let a ← projectionNormalizeHead 60 a
        let b ← projectionNormalizeHead 60 b
        if a == b then
          if t.isHEq then g.hrefl else g.refl
          return
        if a.isFVar && b.isFVar then
          let t' ← if t.isHEq then Lean.Meta.mkHEq a b else Lean.Meta.mkEq a b
          let g' ← g.change t'
          if t.isHEq then g'.assumption
          else
            try g'.assumption
            catch _ =>
              let gs ← g'.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
                { synthAssignedInstances := false }
              for goal in gs do goal.assumption
          return
        let coherence? := if a.getAppFn.isConstOf ``ULift.ring then
          some ``coefficient_ulift_ring
          else if a.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
            some ``coefficient_braided
          else none
        if let some name := coherence? then
          let pf ← Lean.Meta.mkAppOptM name #[some (a.getAppArgs[0]!), none]
          let pf ← if t.isHEq then Lean.Meta.mkAppM ``heq_of_eq #[pf] else pure pf
          let gs ← g.apply pf { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
          let pf ← Lean.instantiateMVars (Lean.mkMVar g)
          cache.modify (·.insert t pf)
          return
        let common := a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0
        let a ← if common then pure a else
          projectionNormalizeHead 60 (← Lean.Meta.whnfD a)
        let b ← if common then pure b else
          projectionNormalizeHead 60 (← Lean.Meta.whnfD b)
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.isLambda || b.isLambda then
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
          throwError "unsupported coefficient congruence at fuel {fuel}:\n{a}\nversus\n{b}"
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

end AlgebraicGeometry.ProEtale.SpTowerShriek
