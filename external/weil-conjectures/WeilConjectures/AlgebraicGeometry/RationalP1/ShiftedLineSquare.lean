/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.ShiftedTateLineComposition
import Mathlib.Logic.Function.Basic
import Mathlib.Lean.Meta.CongrTheorems
import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.AmbientSquareAssembly
import all WeilConjectures.AlgebraicGeometry.RationalP1.DerivedCalculationInstances
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
/-! # The shifted rational Tate-line square

## Implementation details

The square is obtained by lifting the prescribed underived composition equation through
degree zero and the canonical shift.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local instance 30000] cachedModuleClosed
attribute [local instance] CondensedRing.pullback_commShift
attribute [local instance] CondensedRing.cachedFour CondensedRing.cachedGood12
  CondensedRing.cachedGood23 CondensedRing.cachedTensorLeft CondensedRing.cachedTensorRight
  CondensedRing.cachedSheafColimits CondensedRing.cachedSheafBigColimits
  CondensedRing.cachedCoequalizers CondensedRing.cachedModulePreadditive
  CondensedRing.cachedModuleFlatResolution CondensedRing.cachedExactSequential
  CondensedRing.cachedTensorLeftSequential CondensedRing.cachedTensorRightSequential

attribute [local irreducible] Functor.leftDerivedFunctor CondensedRing.upperStar
  upperStarFromPoint
  coefficient line shiftedLineComparison DerivedCategory.singleFunctors
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CondensedRing.leftDerivedUpperStarComp

attribute [local irreducible] firstProjection secondProjection square diagram trace singleUnitIso
  condensedAmbientExchange condensedAmbientPullbackComparison secondLineComparison

set_option allowUnsafeReducibility true in
attribute [local reducible] QuotientChange.L CondensedRing.moduleObjectDerivedPullback

private theorem scalar_pullback_composition_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U V W : Scheme.{u}}
    (a : U ⟶ V) (b : V ⟶ W) :
    QuotientChange.scalarPullbackComposition Λ a b =
      CondensedRing.leftDerivedUpperStarComp Λ a b := by
  unfold QuotientChange.scalarPullbackComposition
  rfl

private theorem scalar_ambient_comparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    ((QuotientChange.scalarPullbackComposition Λ f' g).symm ≪≫
      eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
        sq.toCommSq.w.symm) ≪≫ QuotientChange.scalarPullbackComposition Λ g' f) =
      condensedAmbientPullbackComparison Λ sq := by
  unfold condensedAmbientPullbackComparison
  exact congrArg₂ (fun i j ↦ i.symm ≪≫
    eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
      sq.toCommSq.w.symm) ≪≫ j)
    (scalar_pullback_composition_eq Λ f' g) (scalar_pullback_composition_eq Λ g' f)

private theorem scalar_native_assembly
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (QuotientChange.Modules Λ Y)}
    {B : DerivedCategory (QuotientChange.Modules Λ X)}
    {B' : DerivedCategory (QuotientChange.Modules Λ Y')}
    {Q : DerivedCategory (QuotientChange.Modules Λ X')}
    (e : (moduleObjectDerivedPullback Λ f).obj A ⟶ B)
    (j : (moduleObjectDerivedPullback Λ g).obj A ⟶ B')
    (d : (moduleObjectDerivedPullback Λ g').obj B ⟶ Q)
    (e₂ : (moduleObjectDerivedPullback Λ f').obj B' ⟶ Q)
    (h : ((QuotientChange.scalarPullbackComposition Λ f' g).symm ≪≫
      eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
        sq.toCommSq.w.symm) ≪≫ QuotientChange.scalarPullbackComposition Λ g' f).hom.app A ≫
      (show (QuotientChange.L Λ g').obj ((QuotientChange.L Λ f).obj A) ⟶ Q from
        (QuotientChange.L Λ g').map e ≫ d) =
      (show (QuotientChange.L Λ f').obj ((QuotientChange.L Λ g).obj A) ⟶ Q from
        (QuotientChange.L Λ f').map j ≫ e₂)) :
    (condensedAmbientPullbackComparison Λ sq).hom.app A ≫
      (moduleObjectDerivedPullback Λ g').map e ≫ d =
      (moduleObjectDerivedPullback Λ f').map j ≫ e₂ := by
  rw [← scalar_ambient_comparison_eq Λ sq]
  exact h

private abbrev scalarLineObject
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (X : Scheme.{u}) : DerivedCategory (QuotientChange.Modules (coefficient l c).X X) :=
  ((DerivedCategory.singleFunctor (Modules (coefficient l c).X X) 0).obj
    (line l c X)) ⟦(2 : ℤ)⟧

private abbrev scalarLineMap
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    (QuotientChange.L (coefficient l c).X f).obj (scalarLineObject l c Y) ⟶
      scalarLineObject l c X := by
  unfold scalarLineObject
  exact (shiftedLineComparison l c f).hom

private theorem scalar_shifted_line_comp
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (QuotientChange.scalarPullbackComposition (coefficient l c).X f g).hom.app
        (scalarLineObject l c Z) ≫
      (show (QuotientChange.L (coefficient l c).X f).obj
        ((QuotientChange.L (coefficient l c).X g).obj (scalarLineObject l c Z)) ⟶
          scalarLineObject l c X from
        (QuotientChange.L (coefficient l c).X f).map (scalarLineMap l c g) ≫
          scalarLineMap l c f) = scalarLineMap l c (f ≫ g) := by
  unfold scalarLineMap scalarLineObject
  rw [scalar_pullback_composition_eq]
  exact shifted_line_comparison_comp l c f g

private theorem scalar_line_transport
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    (eqToIso (congrArg (fun f : X ⟶ Y ↦ QuotientChange.L (coefficient l c).X f)
      h)).hom.app (scalarLineObject l c Y) ≫ scalarLineMap l c b = scalarLineMap l c a := by
  subst b
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

private theorem shifted_line_square_general
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y', Invertible (l : Y'.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    ((QuotientChange.scalarPullbackComposition (coefficient l c).X f' g).symm ≪≫
      eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L (coefficient l c).X a)
        sq.toCommSq.w.symm) ≪≫
      QuotientChange.scalarPullbackComposition (coefficient l c).X g' f).hom.app
        (scalarLineObject l c Y) ≫
      (show (QuotientChange.L (coefficient l c).X g').obj
        ((QuotientChange.L (coefficient l c).X f).obj (scalarLineObject l c Y)) ⟶
          scalarLineObject l c X' from
        (QuotientChange.L (coefficient l c).X g').map (scalarLineMap l c f) ≫
          scalarLineMap l c g') =
      (show (QuotientChange.L (coefficient l c).X f').obj
        ((QuotientChange.L (coefficient l c).X g).obj (scalarLineObject l c Y)) ⟶
          scalarLineObject l c X' from
        (QuotientChange.L (coefficient l c).X f').map (scalarLineMap l c g) ≫
          scalarLineMap l c f') := by
  exact ambient_square_assembly (coefficient l c).X sq
    (scalarLineMap l c f) (scalarLineMap l c g)
    (scalarLineMap l c g') (scalarLineMap l c f')
    (scalarLineMap l c (g' ≫ f)) (scalarLineMap l c (f' ≫ g))
    (scalar_shifted_line_comp l c g' f) (scalar_shifted_line_comp l c f' g)
    (scalar_line_transport l c sq.toCommSq.w.symm)

private theorem diagonal_abelian_eq (X : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian X =
      (CategoryTheory.sheafIsAbelian : Abelian (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) := by
  rfl

private theorem coefficientPiEq {α β : Sort u} {P : α → Sort v}
    {Q : β → Sort v} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

open Lean Meta Elab Tactic in
private meta structure CoefficientCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

/-- Choice values in equal nonempty types are heterogeneously equal. -/
private theorem choice_value_heq {α β : Sort u} (h : α = β)
    (ha : Nonempty α) (hb : Nonempty β) :
    HEq (Classical.choice ha) (Classical.choice hb) := by
  cases h
  rfl

/-- Dependent functions that are pointwise heterogeneously equal are heterogeneously equal. -/
private theorem pointwise_heq {α : Sort u} {P Q : α → Sort v}
    {f : ∀ x, P x} {g : ∀ x, Q x} (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  have hPQ : P = Q := funext (fun x ↦ type_eq_of_heq (h x))
  cases hPQ
  exact heq_of_eq (funext (fun x ↦ eq_of_heq (h x)))

open Lean Meta in
private meta def shareNativeProof (lhs rhs h : Expr) : MetaM Expr := do
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
private meta def nativeHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT CoefficientCongrState MetaM Expr := do
  match fuel with
  | 0 => throwError "native congruence exhausted: {lhs}\n{rhs}"
  | next + 1 =>
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if lhs == rhs then return ← mkHEqRefl lhs
    for (a, b, h) in (← get).proofs do
      if a == lhs && b == rhs then return h
    let prove : StateRefT CoefficientCongrState MetaM Expr := do
      let isLineAlias (e : Expr) : Bool :=
        e.isAppOf ``scalarQLineIso || e.isAppOf ``firstLineComparisonForTrace ||
          e.isAppOf ``secondLineComparison
      if isLineAlias lhs then
        if let some lhs' ← withTransparency .all (unfoldDefinition? lhs) then
          return ← nativeHEq lhs' rhs next
      if isLineAlias rhs then
        if let some rhs' ← withTransparency .all (unfoldDefinition? rhs) then
          return ← nativeHEq lhs rhs' next
      if lhs.isAppOf ``AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian &&
          rhs.isAppOf ``CategoryTheory.sheafIsAbelian then
        return ← mkHEqOfEq (← mkAppM ``diagonal_abelian_eq #[lhs.getAppArgs[0]!])
      if rhs.isAppOf ``AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian &&
          lhs.isAppOf ``CategoryTheory.sheafIsAbelian then
        let he ← mkAppM ``diagonal_abelian_eq #[rhs.getAppArgs[0]!]
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
        let ht ← mkEqOfHEq (← nativeHEq xs[0]! ys[0]! next)
        return ← mkAppM ``choice_value_heq #[ht, xs[1]!, ys[1]!]
      match lhs, rhs with
      | .lam n α body _, .lam _ β body' _ =>
        if α == β then
          let init ← get
          let hfun ← withLocalDeclD n α fun x => do
            let h ← nativeHEq (body.instantiate1 x) (body'.instantiate1 x) next
            mkLambdaFVars #[x] h
          let congrs := (← get).congrs
          set { init with congrs := congrs }
          let ty ← whnf (← inferType lhs)
          let ty' ← whnf (← inferType rhs)
          let P := mkLambda n .default α ty.bindingBody!
          let Q := mkLambda n .default α ty'.bindingBody!
          return ← mkAppOptM ``pointwise_heq #[some α, some P, some Q,
            some lhs, some rhs, some hfun]
        let hα ← mkEqOfHEq (← nativeHEq α β next)
        let init ← get
        let hfun ← withLocalDeclD n α fun x =>
          withLocalDeclD (n.appendAfter "'") β fun y => do
          withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
            modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
            let h ← nativeHEq (body.instantiate1 x) (body'.instantiate1 y) next
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
        let hα ← mkEqOfHEq (← nativeHEq α β next)
        let P := mkLambda n .default α body
        let Q := mkLambda n .default β body'
        let hPQ ← nativeHEq P Q next
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
        return ← nativeHEq lhs' rhs' next
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
            let h ← nativeHEq xs[i]! ys[i]! next
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
            return ← nativeHEq lhs' rhs' next
      let lhs' ← whnf lhs
      let rhs' ← whnf rhs
      if lhs' != lhs || rhs' != rhs then
        return ← nativeHEq lhs' rhs' next
      let lhs' := (← unfoldDefinition? lhs).getD lhs
      let rhs' := (← unfoldDefinition? rhs).getD rhs
      if lhs' != lhs || rhs' != rhs then
        return ← nativeHEq lhs' rhs' next
      throwError "coefficient congruence stuck:
  {lhs}
  {rhs}"
    let h ← prove
    let h ← shareNativeProof lhs rhs h
    modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
    return h
termination_by structural fuel

private theorem shifted_line_square_native
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y', Invertible (l : Y'.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    type_of% (scalar_native_assembly (coefficient l c).X sq
      (scalarLineMap l c f) (scalarLineMap l c g)
      (scalarLineMap l c g') (scalarLineMap l c f') (shifted_line_square_general l c sq)) :=
  scalar_native_assembly (coefficient l c).X sq
    (scalarLineMap l c f) (scalarLineMap l c g)
    (scalarLineMap l c g') (scalarLineMap l c f') (shifted_line_square_general l c sq)

/-- The shifted line square follows from the unshifted comparison equation,
exact single-complex functoriality, and compatibility of the canonical shift. -/
theorem shifted_line_square
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (condensedAmbientPullbackComparison (coefficient l c).X (square Y)).hom.app
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X Y) 0).obj
          (line l c Y)) ⟦(2 : ℤ)⟧) ≫
        (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).map
          (scalarQLineIso l c k p hpl Y).hom ≫
        (firstLineComparisonForTrace l c k p hpl Y).hom =
      (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y)).map
          (scalarQLineIso l c k p hpl Y).hom ≫
        (secondLineComparison l c k p hpl Y).hom := by
  let : ∀ x : Y, Invertible (l : Y.residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _ (Y ↘ Spec (.of k)) x).invertible
  let : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (secondProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  have result := shifted_line_square_native l c (square Y)
  run_tac
    Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let mut result? := none
      for decl in ← Lean.getLCtx do
        if decl.userName.eraseMacroScopes == `result then result? := some decl.toExpr
      let some result := result? | throwError "missing local square proof"
      let lhs ← Lean.Meta.inferType result
      let rhs ← goal.getType
      let (proof, _) ← (nativeHEq lhs rhs).run {}
      let eqProof ← Lean.Meta.mkEqOfHEq proof
      goal.assign (← Lean.Meta.mkAppM ``Eq.mp #[eqProof, result])
      return []

end AlgebraicGeometry.ProEtale.RationalP1
