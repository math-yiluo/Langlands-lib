/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import Mathlib.Logic.Function.Basic
import Mathlib.Lean.Meta.CongrTheorems

/-! # Adjuncts of a local projective-line square
-/

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

private theorem local_square_adjuncts
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (ad : L ⊣ R) (ad' : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (θ : G ⋙ L' ⟶ L ⋙ H)
    {A : C} {B : D} {A' : C'} {B' : D'}
    (x : L.obj A ⟶ B) (y : L'.obj A' ⟶ B')
    (j : G.obj A ⟶ A') (d : H.obj B ⟶ B')
    (h : θ.app A ≫ H.map x ≫ d = L'.map j ≫ y) :
    G.map ((ad.homEquiv _ _) x) ≫
        (mateEquiv ad ad' (TwoSquare.mk _ _ _ _ θ)).app B ≫ R'.map d =
      j ≫ (ad'.homEquiv _ _) y := by
  rw [Adjunction.homEquiv_unit, G.map_comp]
  have hn := (mateEquiv ad ad' (TwoSquare.mk _ _ _ _ θ)).naturality x
  change G.map (R.map x) ≫
      (mateEquiv ad ad' (TwoSquare.mk _ _ _ _ θ)).app B =
    (mateEquiv ad ad' (TwoSquare.mk _ _ _ _ θ)).app (L.obj A) ≫
      R'.map (H.map x) at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Category.assoc,
    unit_mateEquiv ad ad' (TwoSquare.mk _ _ _ _ θ) A]
  simp only [Category.assoc]
  rw [← R'.map_comp, ← R'.map_comp]
  change ad'.unit.app (G.obj A) ≫ R'.map (θ.app A ≫ H.map x ≫ d) = _
  rw [h, R'.map_comp]
  simpa only [Category.assoc, Adjunction.homEquiv_unit] using
    congrArg (fun k ↦ k ≫ R'.map y) (ad'.unit_naturality j)

private theorem condensed_local_square_adjuncts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (Modules Λ Y)} {B : DerivedCategory (Modules Λ X)}
    {A' : DerivedCategory (Modules Λ Y')} {B' : DerivedCategory (Modules Λ X')}
    (x : (moduleObjectDerivedPullback Λ f).obj A ⟶ B)
    (y : (moduleObjectDerivedPullback Λ f').obj A' ⟶ B')
    (j : (moduleObjectDerivedPullback Λ g).obj A ⟶ A')
    (d : (moduleObjectDerivedPullback Λ g').obj B ⟶ B')
    (h : (ambientPullbackComparison Λ sq).hom.app A ≫
        (moduleObjectDerivedPullback Λ g').map x ≫ d =
      (moduleObjectDerivedPullback Λ f').map j ≫ y) :
    (moduleObjectDerivedPullback Λ g).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _ x) ≫
        (condensedAmbientExchange Λ sq).app B ≫
        (moduleObjectDerivedPushforward Λ f').map d =
      j ≫ (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f').homEquiv _ _ y := by
  refine Eq.mp ?_ (local_square_adjuncts
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f')
    _ _ (condensedAmbientPullbackComparison Λ sq).hom x y j d ?_)
  · run_tac coefficientCongrGoal
  · refine Eq.mp ?_ h
    run_tac coefficientCongrGoal

/-- A commuting square of local arrows gives the corresponding square of adjuncts
under the fixed projective-line exchange map. -/
theorem p1_local_square_adjuncts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    {A : DerivedCategory (Modules Λ Y)}
    {B A' : DerivedCategory (Modules Λ (ProjectiveLine Y))}
    {B' : DerivedCategory (Modules Λ (diagonalSurface Y))}
    (x : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj A ⟶ B)
    (y : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj A' ⟶ B')
    (j : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj A ⟶ A')
    (d : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj B ⟶ B')
    (h : (ambientPullbackComparison Λ (square Y)).hom.app A ≫
        (moduleObjectDerivedPullback Λ (firstProjection Y)).map x ≫ d =
      (moduleObjectDerivedPullback Λ (secondProjection Y)).map j ≫ y) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ
          (ProjectiveLine Y ↘ Y)).homEquiv _ _ x) ≫
        secondPretraceExchangeMap Λ Y B ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map d =
      j ≫ (CondensedRing.derivedUpperStarLowerStarAdjunction Λ
        (secondProjection Y)).homEquiv _ _ y := by
  refine Eq.mp ?_ (condensed_local_square_adjuncts Λ (square Y) x y j d h)
  run_tac coefficientCongrGoal

end AlgebraicGeometry.ProEtale.RationalP1
