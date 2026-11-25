/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernLocalFactorization
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarLocalChernPullback
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMate
import Mathlib.Logic.Function.Basic
import Mathlib.Lean.Meta.CongrTheorems

/-! # Specialized coefficient cases for scalar Chern exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

-- Build explicit congruence proofs without reducing sheafification constructions.
private theorem coefficientPiEq {α β : Sort v} {P : α → Sort w}
    {Q : β → Sort w} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

open Lean Meta Elab Tactic in
private meta structure CoefficientCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

open Lean Meta Elab Tactic in
private meta partial def coefficientHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT CoefficientCongrState MetaM Expr := do
  if lhs == rhs then return ← mkHEqRefl lhs
  for (a, b, h) in (← get).proofs do
    if a == lhs && b == rhs then return h
  if fuel == 0 then throwError "coefficient congruence exhausted: {lhs}
{rhs}"
  let next := fuel - 1
  let prove : StateRefT CoefficientCongrState MetaM Expr := do
    if (← isProof lhs) && (← isProof rhs) then
      return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
    if lhs.getAppFn.isConstOf ``id && lhs.getAppArgs.size == 2 then
      return ← coefficientHEq lhs.getAppArgs.back! rhs next
    if rhs.getAppFn.isConstOf ``id && rhs.getAppArgs.size == 2 then
      return ← coefficientHEq lhs rhs.getAppArgs.back! next
    let wrappers : Array Name := #[``Modules, ``unit, ``coefficient, ``line,
      ``scalarQChern, ``scalarP2Chern, ``moduleObjectDerivedPullback,
      ``moduleObjectDerivedPushforward, ``condensedAmbientExchange,
      ``ambientPullbackComparison, ``secondPretraceExchangeMap, ``secondTraceExchange]
    if lhs.getAppFn != rhs.getAppFn then
      if let .const name _ := lhs.getAppFn then
        if wrappers.contains name then
          if let some v ← withTransparency .all (unfoldDefinition? lhs) then
            return ← coefficientHEq v rhs next
      if let .const name _ := rhs.getAppFn then
        if wrappers.contains name then
          if let some v ← withTransparency .all (unfoldDefinition? rhs) then
            return ← coefficientHEq lhs v next
    match lhs, rhs with
    | .lam n α body _, .lam _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let init ← get
      let hfun ← withLocalDeclD n α fun x =>
        withLocalDeclD (n.appendAfter "'") β fun y => do
        withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
          modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
          let h ← coefficientHEq (body.instantiate1 x) (body'.instantiate1 y) next
          mkLambdaFVars #[x, y, hxy] h
      let congrs := (← get).congrs
      set { init with congrs := congrs }
      let ty ← whnf (← inferType lhs)
      let ty' ← whnf (← inferType rhs)
      let P := mkLambda n .default α ty.bindingBody!
      let Q := mkLambda n .default β ty'.bindingBody!
      return ← mkAppOptM ``Function.hfunext #[some α, some β, some P, some Q,
        some lhs, some rhs, some hα, some hfun]
    | .forallE n α body _, .forallE _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let P := mkLambda n .default α body
      let Q := mkLambda n .default β body'
      let hPQ ← coefficientHEq P Q next
      let h ← mkAppOptM ``coefficientPiEq #[some α, some β, some P, some Q,
        some hα, some hPQ]
      return ← mkHEqOfEq h
    | _, _ => pure ()
    let expandProjection (e : Expr) : MetaM Expr := do
      let .proj typeName index major := e.getAppFn | return e
      let info := Lean.getStructureInfo (← getEnv) typeName
      let p ← mkProjection major info.fieldNames[index]!
      return mkAppN p e.getAppArgs
    let lhs' ← expandProjection lhs
    let rhs' ← expandProjection rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if f == g && xs.size == ys.size && !xs.isEmpty then
      let init ← get
      try
        let mut found := none
        for (ff, arity, thm) in (← get).congrs do
          if ff == f && arity == xs.size then found := some thm
        let thm? ← match found with
          | some thm => pure (some thm)
          | none => do
            let thm? ← if let .const name levels := f then
              mkHCongrWithArityForConst? name levels xs.size
            else
              try pure (some (← mkHCongrWithArity f xs.size))
              catch _ => pure none
            if let some thm := thm? then
              modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
            pure thm?
        if let some thm := thm? then
          let mut args := #[]
          for i in [:xs.size] do
            let h ← coefficientHEq xs[i]! ys[i]! next
            let h ← if thm.argKinds[i]! == .eq then mkEqOfHEq h else pure h
            args := args ++ #[xs[i]!, ys[i]!, h]
          let h := mkAppN thm.proof args
          let ty ← inferType h
          if ty.isHEq then return h else return ← mkHEqOfEq h
        else
          let ty ← whnf (← inferType lhs)
          let ty' ← whnf (← inferType rhs)
          if ty.isForall && ty'.isForall then
            let lhs' := mkLambda ty.bindingName! .default ty.bindingDomain!
              (mkApp (lhs.liftLooseBVars 0 1) (.bvar 0))
            let rhs' := mkLambda ty'.bindingName! .default ty'.bindingDomain!
              (mkApp (rhs.liftLooseBVars 0 1) (.bvar 0))
            return ← coefficientHEq lhs' rhs' next
      -- Some wrappers ignore parameters. If argumentwise congruence fails, unfold
      -- the wrapper below and compare its values instead.
      catch _ => set init
    let lhs' ← whnf lhs
    let rhs' ← whnf rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let lhs' := (← unfoldDefinition? lhs).getD lhs
    let rhs' := (← unfoldDefinition? rhs).getD rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    throwError "coefficient congruence stuck:
{lhs}
{rhs}"
  let h ← prove
  modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
  return h

open Lean Meta Elab Tactic in
private meta def coefficientCongrGoal : TacticM Unit := do
  liftMetaTactic fun goal => goal.withContext do
    let ty ← goal.getType
    let some (_, lhs, rhs) := ty.eq? | throwError "expected equality"
    let (h, _) ← (coefficientHEq lhs rhs).run {}
    goal.assign (← mkEqOfHEq h)
    return []

attribute [local irreducible] coefficient line firstProjection secondProjection square
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor

-- Keep the large coefficient constructions folded during the mate specialization.
/-- The scalar exchange preserves the positive Chern generator equation in the `some`
coefficient case. -/
theorem scalar_chern_base_change_chern_some
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l (some E)).X
    let cq := scalarQChern l (some E) Y r a
    let c₂ := scalarP2Chern l (some E) Y r b
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    F.map cq ≫ secondTraceExchange l (some E) k p hpl Y =
        (scalarUnitPullIso Λ Y).hom ≫ c₂ := by
  dsimp only
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    have hl : IsUnit (l : k) :=
      (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
        (fun h ↦ hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (Fact.out : l.Prime)).1 h))
    simpa only [map_natCast] using
      hl.map ((Y ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  obtain ⟨z, w, hz, hw, hq, h₂⟩ := scalar_chern_local_factorization l E Y r hY a ha b hb
  rw [hq, h₂]
  have hlocal := scalar_local_chern_pullback l E k p hpl Y δ family r z hz w hw
  refine Eq.mp ?_ (p1_local_square_adjuncts (coefficient l (some E)).X Y
    ((scalarUnitPullIso (coefficient l (some E)).X Y).hom ≫ scalarQLocalChern l E Y r z)
    ((scalarP2UnitIso (coefficient l (some E)).X Y).hom ≫ scalarP2LocalChern l E Y r w)
    (scalarUnitPullIso (coefficient l (some E)).X Y).hom
    (firstLineComparisonForTrace l (some E) k p hpl Y).hom ?_)
  · run_tac coefficientCongrGoal
  · refine Eq.mp ?_ hlocal
    run_tac coefficientCongrGoal

end AlgebraicGeometry.ProEtale.RationalP1
