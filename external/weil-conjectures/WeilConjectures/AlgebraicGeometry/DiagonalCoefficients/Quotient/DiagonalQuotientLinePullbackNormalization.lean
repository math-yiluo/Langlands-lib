/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.ScalarPullbackSingleTransposes
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Quotient line normalization of the scalar/pullback mate

Source: diagonal coefficient changes, paragraph (3), line endpoint normalization.
(blueprint: lem-diagonal-quotient-line-pullback-normalization).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Share the named sheaf structures used by the diagonal coefficient definitions.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

private theorem tensor_unit_square
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal]
    {A : C} [MonObj A] {B : D} [MonObj B]
    (α : F.obj A ⟶ B) [IsMonHom α]
    {M Q : C} {N Q' : D} (r : F.obj M ⟶ N) (q : F.obj Q ⟶ Q')
    (t : A ⊗ M ⟶ Q) (t' : B ⊗ N ⟶ Q')
    (h : F.map t ≫ q = Functor.OplaxMonoidal.δ F A M ≫ (α ⊗ₘ r) ≫ t') :
    F.map ((λ_ M).inv ≫ η[A] ▷ M ≫ t) ≫ q =
      r ≫ (λ_ N).inv ≫ η[B] ▷ N ≫ t' := by
  have hu : F.map η[A] ≫ α = Functor.OplaxMonoidal.η F ≫ η[B] := by
    rw [← cancel_epi (Functor.LaxMonoidal.ε F)]
    simp only [← Category.assoc, ← Functor.obj.η_def, IsMonHom.one_hom]
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [h, ← Functor.OplaxMonoidal.δ_natural_left_assoc]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, hu, comp_whiskerRight, Category.assoc,
    ← Functor.OplaxMonoidal.left_unitality_assoc]
  rw [← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

private theorem coefficient_unit_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules R S) (N : Modules R X)
    (r : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (q : (upperStar Ab.{u + 1} f).obj
      ((Mod.extendScalars (coefficientMap a S)).obj M).X ⟶
      ((Mod.extendScalars (coefficientMap a X)).obj N).X)
    (h : (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap a S) M) ≫ q =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj T S) M.X ≫
        (condensedPullbackHom T f ⊗ₘ r) ≫ Mod.extendπ (coefficientMap a X) N) :
    (upperStar Ab.{u + 1} f).map (Mod.extendUnitHom (coefficientMap a S) M) ≫ q =
      r ≫ Mod.extendUnitHom (coefficientMap a X) N := by
  unfold Mod.extendUnitHom
  exact tensor_unit_square (upperStar Ab.{u + 1} f)
    (condensedPullbackHom T f) r q _ _ h

private theorem unit_cast_heq {α β : Sort v} (h : α = β) (a : α) :
    HEq (Eq.mp h a) a := by
  cases h
  rfl

private theorem unit_diagonalAbelian_eq (X : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian X =
      (CategoryTheory.sheafIsAbelian : Abelian (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) := by
  rfl

private theorem unitPiEq {α β : Sort u} {P : α → Sort v}
    {Q : β → Sort v} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

open Lean Meta Elab Tactic in
private meta structure UnitCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

/-- Equality of the types identifies choice values by proof irrelevance. -/
private theorem unit_choice_heq {α β : Sort u} (h : α = β)
    (ha : Nonempty α) (hb : Nonempty β) :
    HEq (Classical.choice ha) (Classical.choice hb) := by
  cases h
  rfl

/-- Compare dependent functions at a shared argument before transporting the family. -/
private theorem unit_pointwise_heq {α : Sort u} {P Q : α → Sort v}
    {f : ∀ x, P x} {g : ∀ x, Q x} (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  have hPQ : P = Q := funext (fun x ↦ type_eq_of_heq (h x))
  cases hPQ
  exact heq_of_eq (funext (fun x ↦ eq_of_heq (h x)))

open Lean Meta in
private meta def shareUnitNativeProof (lhs rhs h : Expr) : MetaM Expr := do
  let mut val ← instantiateMVars h
  let mut ty ← mkHEq lhs rhs
  let mut used := (collectFVars (collectFVars {} val) ty).fvarIds
  let mut xs := #[]
  for decl in (← getLCtx).decls.toArray.reverse do
    if let some decl := decl then
      if used.contains decl.fvarId then
        xs := #[decl.toExpr] ++ xs
        used := used ++ (collectFVars {} decl.type).fvarIds
        if let some value := decl.value? then
          used := used ++ (collectFVars {} value).fvarIds
  let mut args := #[]
  for x in xs do
    if !(← x.fvarId!.getDecl).isLet then args := args.push x
  for x in xs.reverse do
    let decl ← x.fvarId!.getDecl
    let domain ← instantiateMVars decl.type
    let vb := val.abstract #[x]
    let tb := ty.abstract #[x]
    if let some value := decl.value? then
      let value ← instantiateMVars value
      val := .letE decl.userName domain value vb false
      ty := .letE decl.userName domain value tb false
    else
      val := .lam decl.userName domain vb decl.binderInfo
      ty := .forallE decl.userName domain tb decl.binderInfo
  val ← instantiateMVars val
  ty ← instantiateMVars ty
  if val.hasExprMVar || ty.hasExprMVar then
    throwError "unresolved native auxiliary metavariable"
  let levels := (collectLevelParams (collectLevelParams {} val) ty).params.toList
  let name ← try mkAuxLemma levels ty val
    catch err => throwError "native auxiliary for {lhs.getAppFn}: {err.toMessageData}"
  return mkAppN (mkConst name (levels.map Level.param)) args

-- Build heterogeneous congruence proofs across the existing category-instance aliases.
-- Each auxiliary proof is kernel checked; choice uses proof irrelevance at equal types.
open Lean Meta Elab Tactic in
private meta def unitNativeHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT UnitCongrState MetaM Expr := do
  match fuel with
  | 0 => throwError "native congruence exhausted: {lhs}\n{rhs}"
  | next + 1 =>
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if lhs == rhs then return ← mkHEqRefl lhs
    for (a, b, h) in (← get).proofs do
      if a == lhs && b == rhs then return h
    let prove : StateRefT UnitCongrState MetaM Expr := do
      let isUnitAlias (e : Expr) : Bool :=
        e.isAppOf ``quotientLineMap || e.isAppOf ``quotientLine ||
          e.isAppOf ``QuotientPullMap || e.isAppOf ``Mod.extendUnitHom
      if isUnitAlias lhs then
        if let some lhs' ← withTransparency .all (unfoldDefinition? lhs) then
          return ← unitNativeHEq lhs' rhs next
      if isUnitAlias rhs then
        if let some rhs' ← withTransparency .all (unfoldDefinition? rhs) then
          return ← unitNativeHEq lhs rhs' next
      if lhs.isAppOfArity ``Eq.mp 4 then
        let args := lhs.getAppArgs
        let h₁ ← mkAppM ``unit_cast_heq #[args[2]!, args[3]!]
        let h₂ ← unitNativeHEq args[3]! rhs next
        return ← mkAppM ``HEq.trans #[h₁, h₂]
      if rhs.isAppOfArity ``Eq.mp 4 then
        let args := rhs.getAppArgs
        let h₁ ← unitNativeHEq lhs args[3]! next
        let h₂ ← mkAppM ``unit_cast_heq #[args[2]!, args[3]!]
        return ← mkAppM ``HEq.trans #[h₁, ← mkAppM ``HEq.symm #[h₂]]
      if lhs.isAppOf ``AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian &&
          rhs.isAppOf ``CategoryTheory.sheafIsAbelian then
        return ← mkHEqOfEq (← mkAppM ``unit_diagonalAbelian_eq #[lhs.getAppArgs[0]!])
      if rhs.isAppOf ``AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian &&
          lhs.isAppOf ``CategoryTheory.sheafIsAbelian then
        let he ← mkAppM ``unit_diagonalAbelian_eq #[rhs.getAppArgs[0]!]
        return ← mkHEqOfEq (← mkAppM ``Eq.symm #[he])
      if (← isProof lhs) && (← isProof rhs) then
        return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      let lhsType ← whnf (← inferType lhs)
      let rhsType ← whnf (← inferType rhs)
      if lhsType.isForall && rhsType.isForall &&
          lhsType.bindingBody!.isAppOf ``Invertible &&
          rhsType.bindingBody!.isAppOf ``Invertible then
        if lhsType == rhsType then
          return ← mkHEqOfEq (← mkAppM ``Subsingleton.elim #[lhs, rhs])
      if lhs.isAppOfArity ``Classical.choice 2 && rhs.isAppOfArity ``Classical.choice 2 then
        let xs := lhs.getAppArgs
        let ys := rhs.getAppArgs
        let ht ← mkEqOfHEq (← unitNativeHEq xs[0]! ys[0]! next)
        return ← mkAppM ``unit_choice_heq #[ht, xs[1]!, ys[1]!]
      match lhs, rhs with
      | .lam n α body _, .lam _ β body' _ =>
        if α == β then
          let init ← get
          let hfun ← withLocalDeclD n α fun x => do
            let h ← unitNativeHEq (body.instantiate1 x) (body'.instantiate1 x) next
            mkLambdaFVars #[x] h
          let congrs := (← get).congrs
          set { init with congrs := congrs }
          let ty ← whnf (← inferType lhs)
          let ty' ← whnf (← inferType rhs)
          let P := mkLambda n .default α ty.bindingBody!
          let Q := mkLambda n .default α ty'.bindingBody!
          return ← mkAppOptM ``unit_pointwise_heq #[some α, some P, some Q,
            some lhs, some rhs, some hfun]
        let hα ← mkEqOfHEq (← unitNativeHEq α β next)
        let init ← get
        let hfun ← withLocalDeclD n α fun x =>
          withLocalDeclD (n.appendAfter "'") β fun y => do
          withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
            modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
            let h ← unitNativeHEq (body.instantiate1 x) (body'.instantiate1 y) next
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
        let hα ← mkEqOfHEq (← unitNativeHEq α β next)
        let P := mkLambda n .default α body
        let Q := mkLambda n .default β body'
        let hPQ ← unitNativeHEq P Q next
        let h ← mkAppOptM ``unitPiEq #[some α, some β, some P, some Q,
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
        return ← unitNativeHEq lhs' rhs' next
      let mut f := lhs.getAppFn
      let mut g := rhs.getAppFn
      let mut xs := lhs.getAppArgs
      let mut ys := rhs.getAppArgs
      if f == g && xs.size == ys.size then
        let mut same := 0
        while same < xs.size && xs[same]! == ys[same]! do
          same := same + 1
        f := mkAppN f (xs.extract 0 same)
        g := mkAppN g (ys.extract 0 same)
        xs := xs.extract same xs.size
        ys := ys.extract same ys.size
      if f == g && xs.size == ys.size && !xs.isEmpty then
        let mut found := none
        for (ff, arity, thm) in (← get).congrs do
          if ff == f && arity == xs.size then found := some thm
        let thm? ← match found with
          | some thm => pure (some thm)
          | none => do
            let optimized? ← if let .const name levels := f then
              mkHCongrWithArityForConst? name levels xs.size
            else pure none
            let thm? ← match optimized? with
              | some thm => pure (some thm)
              | none =>
                try pure (some (← mkHCongrWithArity f xs.size))
                catch _ => pure none
            if let some thm := thm? then
              modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
            pure thm?
        if let some thm := thm? then
          let mut args := #[]
          for i in [:xs.size] do
            let h ← unitNativeHEq xs[i]! ys[i]! next
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
            return ← unitNativeHEq lhs' rhs' next
      let lhs' ← whnf lhs
      let rhs' ← whnf rhs
      if lhs' != lhs || rhs' != rhs then
        return ← unitNativeHEq lhs' rhs' next
      let lhs' := (← unfoldDefinition? lhs).getD lhs
      let rhs' := (← unfoldDefinition? rhs).getD rhs
      if lhs' != lhs || rhs' != rhs then
        return ← unitNativeHEq lhs' rhs' next
      throwError "coefficient congruence stuck:
  {lhs}
  {rhs}"
    let h ← prove
    let h ← shareUnitNativeProof lhs rhs h
    modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
    return h
termination_by structural fuel

-- Replace implicit definitional conversions at each application argument by
-- kernel-checked heterogeneous congruence, then transport the final proposition.
open Lean Meta Elab Tactic in
local elab "unit_native_exact " t:term : tactic => do
  withMainContext do
    let goal ← getMainGoal
    let raw ← Term.elabTerm t (some (← goal.getType))
    Term.synthesizeSyntheticMVarsNoPostponing
    let raw := (← instantiateMVars raw).consumeMData
    if raw.hasMVar then throwError "Unresolved unit proof arguments"
    let rebuild : StateRefT UnitCongrState MetaM Expr := do
      let mut result := raw.getAppFn
      for arg in raw.getAppArgs do
        let ty ← whnf (← inferType result)
        unless ty.isForall do throwError "The unit helper is not a function"
        let expected := ty.bindingDomain!
        let actual ← inferType arg
        let mut arg := arg
        if actual != expected then
          let h ← mkEqOfHEq (← unitNativeHEq actual expected)
          arg ← mkAppM ``Eq.mp #[h, arg]
        result := mkApp result arg
      let actual ← inferType result
      let expected ← goal.getType
      let h ← mkEqOfHEq (← unitNativeHEq actual expected)
      mkAppM ``Eq.mp #[h, result]
    let (proof, _) ← rebuild.run {}
    if proof.hasSorry then throwError "Unfinished unit conversion proof"
    goal.assign proof
    replaceMainGoal []

attribute [local irreducible] spIntegralTwist spIntegralComparison

-- Explicit congruence creates shared auxiliary proofs for the sheaf-instance aliases.
attribute [local irreducible] derivedUpper
  singlePullback PullEndpoint.shift Endpoint.shift scalarPullbackComparison
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
