/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleChartExchangePasting
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents

/-! # Identifying the recorded diagonal chart transport

Source: blueprint thm-amb-p1-adjunction.proof.md, selected projection chart. -/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  AlgebraicGeometry.ProjectiveSpace derivedUpperStarLowerStarAdjunction
  rightDerivedLowerStarComp rightDerivedLowerStarCongr
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.mapDerivedCategory

-- Compare recorded instances without expanding the derived localization constructions.
private meta def unfoldBoundary (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if let .fvar id := e then
    if let some v := (← id.getDecl).value? then return some v
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  let names : List Lean.Name := [``DerivedCategoryModule, ``ordinaryFinitePushforward,
    ``ordinaryFinitePullback, ``ordinaryFiniteP1DiagonalTarget,
    ``ordinaryFiniteP1DiagonalChartMap, ``ordinaryFiniteChartTransport,
    ``ordinaryFiniteAdjunction, ``derivedChartCoefficientMap,
    ``chartCoefficientComposite]
  if let some n := e.getAppFn.constName? then
    if names.contains n then
      return ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e)
  return none

private meta def reduceRecordProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  let some n := e.getAppFn.constName? | return none
  let some info ← Lean.getProjectionFnInfo? n | return none
  let args := e.getAppArgs
  unless args.size == info.numParams + 1 do return none
  let v ← Lean.Meta.withTransparency .all (Lean.Meta.whnf args.back!)
  Lean.Expr.reduceProjStruct? (Lean.mkAppN e.getAppFn (args.set! (args.size - 1) v))

private meta def reduceIdentityObj (e : Lean.Expr) : Lean.Expr := Id.run do
  if e.getAppFn.isConstOf ``Functor.obj then
    let args := e.getAppArgs
    if args.size ≥ 2 && (args[args.size - 2]!).getAppFn.isConstOf ``Functor.id then
      return args.back!
  return e

/-- Build a kernel-checked congruence, treating proof arguments by proof irrelevance. -/
private meta def structuralHEq : Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _ => throwError "chart congruence exhausted its structural depth"
  | fuel + 1, lhs, rhs => do
    let lhs := reduceIdentityObj (← Lean.instantiateMVars lhs).consumeMData.headBeta
    let rhs := reduceIdentityObj (← Lean.instantiateMVars rhs).consumeMData.headBeta
    if lhs == rhs then return ← Lean.Meta.mkHEqRefl lhs
    if let (.const n _, .const m _) := (lhs, rhs) then
      if n == m then return ← Lean.Meta.mkHEqRefl lhs
    if lhs.isSort && rhs.isSort && (← Lean.Meta.isDefEq lhs rhs) then
      return ← Lean.Meta.mkHEqRefl lhs
    if ← Lean.Meta.isProp (← Lean.Meta.inferType lhs) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
    let aa := lhs.getAppArgs
    let bb := rhs.getAppArgs
    let sameHead := lhs.getAppFn == rhs.getAppFn ||
      (lhs.getAppFn.constName?.isSome && lhs.getAppFn.constName? == rhs.getAppFn.constName?)
    unless sameHead && aa.size == bb.size && aa.size > 0 do
      if let some a ← unfoldBoundary lhs then return ← structuralHEq fuel a rhs
      if let some b ← unfoldBoundary rhs then return ← structuralHEq fuel lhs b
      if let some a ← reduceRecordProjection lhs then return ← structuralHEq fuel a rhs
      if let some b ← reduceRecordProjection rhs then return ← structuralHEq fuel lhs b
      if lhs.isLambda || rhs.isLambda then
        if ← Lean.Meta.isDefEq lhs rhs then return ← Lean.Meta.mkHEqRefl lhs
      throwError "chart congruence: {lhs} versus {rhs}"
    let ct ← Lean.Meta.mkHCongrWithArity lhs.getAppFn aa.size
    let mut pf := ct.proof
    for i in [:aa.size] do
      let ih ← structuralHEq fuel aa[i]! bb[i]!
      let arg ← match ct.argKinds[i]! with
        | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
        | .heq => pure ih
        | _ => throwError "unexpected chart congruence argument"
      pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
    if (← Lean.Meta.inferType pf).isEq then
      return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]
    return pf

/-- Generic identification of the recorded chart transport with the canonical derived chart map.
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteChartTransport_eq_derivedChartCoefficientMap
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z) (hr : e ≫ p = r)
    (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    ordinaryFiniteChartTransport A e p r hr L L' v =
      derivedChartCoefficientMap (ModuleCat.{u + 1} A) e p r hr L L' v := by
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let some (_, lhs, rhs) := (← g.getType).eq? | throwError "expected an equality"
      let h ← structuralHEq 200 lhs rhs
      g.assign (← Lean.Meta.mkAppM ``eq_of_heq #[h])
    Lean.Elab.Tactic.replaceMainGoal []

/-- Expand the recorded diagonal chart map and its chart transport. The resulting four factors are
direct image of the adjunction unit, the direct-image composition comparison, the equality
comparison and direct image of the shifted coefficient comparison. Expand the generic chart
coefficient map to the same four factors. The recorded ordinary adjunction is the canonical
derived adjunction by its defining equation, and the recorded ordinary pullback and pushforward
are the canonical derived functors. Replacing these aliases identifies each factor; composition
congruence gives the equality. No projective-line trace or triangle identity is used.

Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteDiagonalChartMap_eq_generic (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
    derivedChartCoefficientMap (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).val.hom (projectiveLineDiagonalProjection S a)
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
      (projectiveLineDiagonalChart S a).property
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
      ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
      (ordinaryFiniteShiftedLinePullback A N hA t
        (projectiveLineDiagonalChart S a).val.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom   := by
  unfold ordinaryFiniteP1DiagonalChartMap
  exact ordinaryFiniteChartTransport_eq_derivedChartCoefficientMap A
    (projectiveLineDiagonalChart S a).val.hom
    (projectiveLineDiagonalProjection S a)
    (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
    (projectiveLineDiagonalChart S a).property _ _ _

end AlgebraicGeometry.Etale
