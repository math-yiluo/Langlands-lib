/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralExchangeTargetAdjunct
import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientPullbackCube
import Mathlib.Logic.Function.Basic
import Mathlib.Lean.Meta.CongrTheorems

/-! # Flat coefficient extension and ambient exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.RationalP1

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedPullIso derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.leftDerivedUpperStarComp condensedAmbientPullbackComparison
  Adjunction.pullIsoOfComapIso Adjunction.pushHomOfComapIso Mod.monoidalCategory
  Mod.monoidalClosed

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward Mod.regular

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
  -- Assigned universe and instance variables must be resolved before matching heads.
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then return ← mkHEqRefl lhs
  for (a, b, h) in (← get).proofs do
    if a == lhs && b == rhs then return h
  if fuel == 0 then throwError "coefficient congruence exhausted: {lhs}
{rhs}"
  let next := fuel - 1
  let prove : StateRefT CoefficientCongrState MetaM Expr := do
    if (← isProof lhs) && (← isProof rhs) then
      return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
    if let .fvar id := lhs then
      if let some value := (← id.getDecl).value? then
        return ← coefficientHEq value rhs next
    if let .fvar id := rhs then
      if let some value := (← id.getDecl).value? then
        return ← coefficientHEq lhs value next
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
      catch ex =>
        if f.isConstOf ``Eq then throw ex
        set init
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

open Lean Elab Tactic in
/-- Close structural instance equalities without unfolding sheafification data. -/
scoped elab "coefficient_congr" : tactic => coefficientCongrGoal

open Lean Meta Elab Tactic in
private meta def coefficientZeta (e : Expr) : MetaM Expr := do
  let mut values : Array (FVarId × Expr) := #[]
  let subst (e : Expr) (values : Array (FVarId × Expr)) : Expr :=
    e.replace fun sub => do
      let .fvar id := sub | none
      (values.find? (fun pair => pair.1 == id)).map Prod.snd
  for decl in (← getLCtx) do
    if let some value := decl.value? then
      let value ← instantiateMVars value
      values := values.push (decl.fvarId, subst value values)
  return subst (← instantiateMVars e) values

open Lean Meta Elab Tactic in
/-- Transport an equality by heterogeneous equalities of its two arrows. -/
scoped elab "coefficient_finish " h:ident : tactic => withMainContext do
  let value ← Elab.Term.elabTerm h none
  liftMetaTactic fun goal => goal.withContext do
    let source ← instantiateMVars (← coefficientZeta (← whnf (← inferType value)))
    let target ← instantiateMVars (← coefficientZeta (← whnf (← goal.getType)))
    if source == target then
      goal.assign value
      return []
    let some (_, lhs, rhs) := source.eq? | throwError "expected source equality"
    let some (_, lhs', rhs') := target.eq? | throwError "expected target equality"
    let (hL, st) ← (coefficientHEq lhs lhs').run {}
    let (hR, _) ← (coefficientHEq rhs rhs').run st
    let hL ← mkAppM ``HEq.symm #[hL]
    let h ← mkAppM ``heq_of_eq #[value]
    let h ← mkAppM ``HEq.trans #[h, hR]
    let h ← mkAppM ``HEq.trans #[hL, h]
    goal.assign (← mkAppM ``eq_of_heq #[h])
    return []

/-- The coefficient/exchange rectangle, with its category and functor instances fixed. -/
def CoefficientExchangeSquare
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {R : C₂ ⥤ C₁} {S : C₄ ⥤ C₃} {Re : D₂ ⥤ D₁} {Se : D₄ ⥤ D₃}
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    (B : R ⋙ G ⟶ H ⋙ S) (Be : Re ⋙ Ge ⟶ He ⋙ Se)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : R ⋙ T₁ ⟶ T₂ ⋙ Re) (δ' : S ⋙ T₃ ⟶ T₄ ⋙ Se) (K : C₂) : Prop :=
    αG.app (R.obj K) ≫ Ge.map (δ.app K) ≫ Be.app (T₂.obj K) =
      T₃.map (B.app K) ≫ δ'.app (H.obj K) ≫ Se.map (αH.app K)

/-- A naturality square for an arrow, with its functors fixed before taking components. -/
def PullArrowSquare
    {C D C' D' : Type w} [Category.{v} C] [Category.{v} D]
    [Category.{v} C'] [Category.{v} D']
    {F : C ⥤ D} {F' : C' ⥤ D'} {T : C ⥤ C'} {U : D ⥤ D'}
    (α : F ⋙ U ≅ T ⋙ F') {V : C} {V' : C'} {W : D} {W' : D'}
    (m : T.obj V ⟶ V') (β : F.obj V ⟶ W) (β' : F'.obj V' ⟶ W')
    (n : U.obj W ⟶ W') : Prop :=
  α.hom.app V ≫ F'.map m ≫ β' = U.map β ≫ n

/-- A scalar endpoint square, keeping the pullback and scalar functors fixed. -/
def PullEndpointSquare
    {C D C' D' : Type w} [Category.{v} C] [Category.{v} D]
    [Category.{v} C'] [Category.{v} D']
    {H : C ⥤ D} {He : C' ⥤ D'} {T : C ⥤ C'} {U : D ⥤ D'}
    (α : H ⋙ U ⟶ T ⋙ He) {K : C} {K' : C'} {W : D} {W' : D'}
    (cK : T.obj K ⟶ K') (e : H.obj K ⟶ W) (e' : He.obj K' ⟶ W')
    (cW : U.obj W ⟶ W') : Prop :=
  α.app K ≫ He.map cK ≫ e' = U.map e ≫ cW

/-- Postcompose the native exchange rectangle with compatible line endpoints. -/
theorem coefficient_exchange_line
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {R : C₂ ⥤ C₁} {S : C₄ ⥤ C₃} {Re : D₂ ⥤ D₁} {Se : D₄ ⥤ D₃}
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    (B : R ⋙ G ⟶ H ⋙ S) (Be : Re ⋙ Ge ⟶ He ⋙ Se)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : R ⋙ T₁ ⟶ T₂ ⋙ Re) (δ' : S ⋙ T₃ ⟶ T₄ ⋙ Se)
    {K : C₂} {K' : D₂} {W : C₄} {W' : D₄}
    (cK : T₂.obj K ⟶ K') (e : H.obj K ⟶ W) (e' : He.obj K' ⟶ W')
    (cW : T₄.obj W ⟶ W')
    (h : CoefficientExchangeSquare B Be αG.hom αH δ δ' K)
    (he : PullEndpointSquare αH cK e e' cW) :
    PullArrowSquare αG (δ.app K ≫ Re.map cK)
      (B.app K ≫ S.map e) (Be.app K' ≫ Se.map e') (δ'.app W ≫ Se.map cW) := by
  unfold PullArrowSquare PullEndpointSquare at *
  unfold CoefficientExchangeSquare at h
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (Be.naturality cK), reassoc_of% h]
  simp only [← Se.map_comp]
  rw [he, Se.map_comp]
  rw [← reassoc_of% (δ'.naturality e)]

/-- Paste the unit and exchange squares through arbitrary right-derived model isomorphisms. -/
theorem transport_scalar_models
    {C D C' D' : Type w} [Category.{v} C] [Category.{v} D]
    [Category.{v} C'] [Category.{v} D']
    {F : C ⥤ D} {F' : C' ⥤ D'} {T : C ⥤ C'} {U : D ⥤ D'}
    (α : F ⋙ U ≅ T ⋙ F')
    {K V V₀ : C} {K' V' V₀' : C'} {J W W₀ : D} {J' W' W₀' : D'}
    (c : T.obj K ≅ K') (c' : U.obj J ≅ J')
    (u : F.obj K ≅ J) (u' : F'.obj K' ≅ J')
    (q : V₀ ≅ V) (q' : V₀' ≅ V') (r : W₀ ≅ W) (r' : W₀' ≅ W')
    (x : K ⟶ V₀) (e : K' ⟶ V₀') (e₂ : J' ⟶ W₀')
    (m : T.obj V ⟶ V') (n : U.obj W ⟶ W')
    (β : F.obj V ⟶ W) (β' : F'.obj V' ⟶ W')
    (hU : PullEndpointSquare α.hom c.hom u.hom u'.hom c'.hom)
    (hβ : PullArrowSquare α m β β' n)
    (hq : e ≫ q'.hom = c.inv ≫ T.map (x ≫ q.hom) ≫ m)
    (h₂ : e₂ ≫ r'.hom = c'.inv ≫
      U.map ((u.inv ≫ F.map (x ≫ q.hom) ≫ β ≫ r.inv) ≫ r.hom) ≫ n) :
    F'.map (e ≫ q'.hom) ≫ β' = u'.hom ≫ e₂ ≫ r'.hom := by
  unfold PullEndpointSquare at hU
  unfold PullArrowSquare at hβ
  rw [hq, h₂]
  simp only [Category.assoc]
  apply (cancel_epi (α.hom.app K ≫ F'.map c.hom)).1
  simp only [Category.assoc]
  rw [reassoc_of% hU]
  simp only [Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_map_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_map_assoc]
  rw [← reassoc_of% (α.hom.naturality x),
    ← reassoc_of% (α.hom.naturality q.hom), hβ]

open Lean Meta Elab Term in
/-- Instantiate the proved paste using the categories and objects already carried
by its arguments. This avoids repeating dependent instance inference; the kernel
checks the resulting application of transport_scalar_models. -/
scoped elab "coefficient_paste% " "[" ts:term,* "]" : term => do
  let es ← ts.getElems.mapM fun t => Elab.Term.elabTerm t none
  unless es.size == 24 do throwError "Expected four functors and twenty paste arguments"
  let sourceFunctor := (← whnf (← inferType es[0]!)).getAppArgs
  let fClosure := (← whnf (← inferType es[1]!)).getAppArgs
  unless sourceFunctor.size == 4 && fClosure.size == 4 do throwError "Expected functors"
  let isoArgs (i : Nat) : MetaM (Array Expr) := do
    let ty ← whnf (← inferType es[i]!)
    unless ty.isAppOf ``CategoryTheory.Iso do throwError "Expected isomorphism"
    pure ty.getAppArgs
  let sourceEndpoint ← isoArgs 5
  let cClosure ← isoArgs 6
  let sourceUnit ← isoArgs 7
  let sourceModel ← isoArgs 9
  let qClosure ← isoArgs 10
  let targetModel ← isoArgs 11
  let rClosure ← isoArgs 12
  let objects := #[sourceUnit[2]!.getAppArgs.back!, sourceModel[3]!, sourceModel[2]!,
    sourceEndpoint[3]!, qClosure[3]!, qClosure[2]!,
    sourceUnit[3]!, targetModel[3]!, targetModel[2]!, cClosure[3]!, rClosure[3]!, rClosure[2]!]
  let categories := #[sourceFunctor[0]!, sourceFunctor[2]!, fClosure[0]!, fClosure[2]!,
    sourceFunctor[1]!, sourceFunctor[3]!, fClosure[1]!, fClosure[3]!]
  let levels := (← whnf (← inferType sourceFunctor[1]!)).getAppFn.constLevels!
  let info ← getConstInfo ``transport_scalar_models
  let levels := info.levelParams.map fun n => if n == `v then levels[0]! else levels[1]!
  return mkAppN (mkConst ``transport_scalar_models levels)
    (categories ++ es[:4].toArray ++ #[es[4]!] ++ objects ++ es[5:].toArray)

private theorem mate_counit_of_eq
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {U : C ⥤ D} {R : D ⥤ C} {V : C' ⥤ D'} {S : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (a : U ⊣ R) (b : V ⊣ S)
    (θ : G ⋙ V ⟶ U ⋙ H) (B : R ⋙ G ⟶ H ⋙ S)
    (h : B = (mateEquiv a b (TwoSquare.mk _ _ _ _ θ))) (K : D) :
    V.map (B.app K) ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K) := by
  subst B
  exact mateEquiv_counit a b _ K

private theorem push_pull_counit_of_eq
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
    {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
    {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
    {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
    (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)
    (α : U₁ ⋙ E₁ ≅ E₂ ⋙ U₂) (δ : L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂)
    (hα : α = Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e)
    (hδ : δ = Adjunction.pushHomOfComapIso adj₁ adj₂ e) (K : A) :
    U₂.map (δ.app K) ≫ adjS.counit.app (E₁.obj K) =
      α.inv.app (L₁.obj K) ≫ E₁.map (adjR.counit.app K) := by
  subst α δ
  exact push_pull_counit adj₁ adj₂ adjR adjS e K

private theorem exchange_of_whole_comparisons
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {U : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
    {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
    (a : U ⊣ R) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    {Q₁ : D₁ ⥤ C₁} {Q₂ : D₂ ⥤ C₂} {Q₃ : D₃ ⥤ C₃} {Q₄ : D₄ ⥤ C₄}
    (s₁ : T₁ ⊣ Q₁) (s₂ : T₂ ⊣ Q₂) (s₃ : T₃ ⊣ Q₃) (s₄ : T₄ ⊣ Q₄)
    (e : Re ⋙ Q₁ ≅ Q₂ ⋙ R) (e' : Se ⋙ Q₃ ≅ Q₄ ⋙ S)
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (B : R ⋙ G ⟶ H ⋙ S) (Be : Re ⋙ Ge ⟶ He ⋙ Se)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : R ⋙ T₁ ⟶ T₂ ⋙ Re) (δ' : S ⋙ T₃ ⟶ T₄ ⋙ Se)
    (hB : B = (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)))
    (hBe : Be = (mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)))
    (hU : αU = Adjunction.pullIsoOfComapIso s₂ s₁ a ae e)
    (hV : αV = Adjunction.pullIsoOfComapIso s₄ s₃ b be e')
    (hδ : δ = Adjunction.pushHomOfComapIso s₂ s₁ e)
    (hδ' : δ' = Adjunction.pushHomOfComapIso s₄ s₃ e')
    (K : C₂) (hcube : Adjunction.coefficientPullbackSquare θ θe αU αV αG αH (R.obj K)) :
    CoefficientExchangeSquare B Be αG αH δ δ' K := by
  exact Adjunction.coefficient_exchange_of_counit_at a b ae be θ θe K
    _ _ (mate_counit_of_eq a b θ B hB K) (mate_counit_of_eq ae be θe Be hBe _)
    αU αV αG αH _ _
    (push_pull_counit_of_eq s₂ s₁ a ae e αU δ hU hδ K)
    (push_pull_counit_of_eq s₄ s₃ b be e' αV δ' hV hδ' _) hcube

/-- Reuse the scalar adjunction arguments already fixed in the native comparison.
Re-elaborating them would choose a different presentation of the sheaf braiding. -/
scoped elab "nativeScalarAdj% " t:term:max n:num : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let some body ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e)
    | throwError "Expected a native scalar/pullback comparison"
  unless body.isAppOf ``Adjunction.pullIsoOfComapIso do
    throwError "Expected the defining conjugate comparison"
  let mut adjs := #[]
  for arg in body.getAppArgs do
    let ty ← Lean.Meta.inferType arg
    if ty.isAppOf ``CategoryTheory.Adjunction then
      adjs := adjs.push arg
  let i := n.getNat
  unless i < 2 && adjs.size == 4 do
    throwError "Expected the four defining adjunctions"
  return adjs[i]!

/-- Flat scalar extension commutes with the canonical ambient exchange mate. -/
theorem flat_coefficient_exchange
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : ChosenCartesianSquare g' f' f g) (K : DerivedCategory (Modules Λ X)) :
    CoefficientExchangeSquare
      (condensedAmbientExchange Λ sq) (condensedAmbientExchange Λ' sq)
      (derivedPullIso a g).hom (derivedPullIso a g').hom
      (derivedPushHom a f) (derivedPushHom a f') K := by
  refine exchange_of_whole_comparisons
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f')
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' f')
    (nativeScalarAdj% (derivedPullIso a f) 1)
    (nativeScalarAdj% (derivedPullIso a f) 0)
    (nativeScalarAdj% (derivedPullIso a f') 1)
    (nativeScalarAdj% (derivedPullIso a f') 0)
    (derivedComapLowerStarIso a f) (derivedComapLowerStarIso a f')
    (condensedAmbientPullbackComparison Λ sq).hom
    (condensedAmbientPullbackComparison Λ' sq).hom _ _
    (derivedPullIso a f) (derivedPullIso a f') _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ K
    (flat_coefficient_pullback_cube a sq _)
  · rfl
  · rfl
  · unfold derivedPullIso
    rfl
  · unfold derivedPullIso
    rfl
  · unfold derivedPushHom
    rfl
  · unfold derivedPushHom
    rfl

end AlgebraicGeometry.ProEtale.RationalP1
