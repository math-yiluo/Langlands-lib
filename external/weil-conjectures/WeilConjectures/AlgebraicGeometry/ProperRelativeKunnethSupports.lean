/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
import WeilConjectures.AlgebraicGeometry.ProperKunnethNormalizationAlgebra
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupports
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-! # Proper support comparison for one relative Kunneth route

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first triangle, comparison of canonical mates.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

set_option Elab.async false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory

private theorem inner_supports_algebra {D : Type v} [Category.{u + 1} D]
    (T : D ⥤ D ⥤ D)
    (s : ∀ M N : D, (T.obj M).obj N ≅ (T.obj N).obj M)
    (hs : ∀ {M M' : D} (a : M ⟶ M') (N : D),
      (T.obj N).map a ≫ (s M' N).inv = (s M N).inv ≫ (T.map a).app N)
    {Z Z' Q Q' K V : D}
    (e : Z ⟶ Q) (c : Q ⟶ Q') (a : Z ⟶ Z') (b : Z' ⟶ Q')
    (r : (T.obj Q).obj K ⟶ V) (r' : (T.obj Q').obj K ⟶ V)
    (hp : r = (T.map c).app K ≫ r') (he : e ≫ c = a ≫ b) :
    (s Z K).inv ≫ (T.map e).app K ≫ r =
      (T.obj K).map a ≫ (s Z' K).inv ≫ (T.map b).app K ≫ r' := by
  rw [hp]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp]
  rw [he]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← reassoc_of% (hs a K)]

private theorem tensor_inputs_swap_algebra {D : Type v} [Category.{u + 1} D]
    (T : D ⥤ D ⥤ D)
    (s : ∀ M N : D, (T.obj M).obj N ≅ (T.obj N).obj M)
    (hL : ∀ {M M' : D} (a : M ⟶ M') (N : D),
      (T.obj N).map a ≫ (s M' N).inv = (s M N).inv ≫ (T.map a).app N)
    (hR : ∀ (M : D) {N N' : D} (b : N ⟶ N'),
      (T.map b).app M ≫ (s M N').inv = (s M N).inv ≫ (T.obj M).map b)
    {M M' N N' : D} (a : M ⟶ M') (b : N ⟶ N') :
    (s N M).inv ≫ (T.map b).app M ≫ (T.obj N').map a =
      (T.map a).app N ≫ (T.obj M').map b ≫ (s N' M').inv := by
  rw [← reassoc_of% (hL b M)]
  rw [← hR N' a]
  rw [(T.map a).naturality_assoc b]

-- Congruence compares construction data without unfolding derived functors.
-- Proof fields are irrelevant even when their propositions have different expressions.
-- The kernel checks the generated equalities, including the coefficient braiding equality.
section ProofTransport

open Lean Meta Elab Tactic

private theorem support_proofs_heq {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  have h : P = Q := propext ⟨fun _ ↦ q, fun _ ↦ p⟩
  cases h
  rfl

private theorem support_forall_congr {D : Sort*} {p q : D → Prop}
    (h : ∀ x, p x = q x) : (∀ x, p x) = (∀ x, q x) :=
  congrArg (fun r : D → Prop ↦ ∀ x, r x) (funext h)

private theorem support_fun_heq {D : Sort v} {E E' : D → Sort u}
    (f : ∀ x, E x) (g : ∀ x, E' x) (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  have he : E = E' := funext fun x ↦ type_eq_of_heq (h x)
  cases he
  exact heq_of_eq (funext fun x ↦ eq_of_heq (h x))

private meta def support_reduce_obj (e : Expr) : MetaM (Option Expr) := do
  unless e.getAppFn.isConstOf ``Functor.obj && e.getAppArgs.size == 6 do return none
  let f := e.getAppArgs[4]!
  unless f.getAppFn.isConstOf ``Functor.obj && f.getAppArgs.size == 6 do return none
  let n := f.getAppArgs[4]!.getAppFn.constName?
  let thm := match n with
    | some ``rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar =>
      some ``rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar_obj_obj
    | some ``derivedTensorRightDerivedLowerStar =>
      some ``derivedTensorRightDerivedLowerStar_obj_obj
    | some ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar =>
      some ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
    | some ``derivedTensorRightDerivedLowerShriek =>
      some ``derivedTensorRightDerivedLowerShriek_obj_obj
    | _ => none
  let some name := thm | return none
  let cs := f.getAppArgs[4]!.getAppArgs
  let pf := mkAppN (← mkConstWithFreshMVarLevels name)
    (cs ++ #[f.getAppArgs[5]!, e.getAppArgs[5]!])
  let some (_, _, rhs) := (← inferType pf).eq?
    | throwError "expected a component equation"
  return some rhs

private meta def support_reduce_quiver (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .proj n i v =>
    if v.getAppFn.isConstOf ``catToReflQuiver then
      let some v' ← withTransparency .all (unfoldDefinition? v)
        | return none
      return some (← withReducible (whnf (.proj n i v')))
  | _ =>
    let ar := e.getAppArgs
    if !ar.isEmpty && ar.back!.getAppFn.isConstOf ``catToReflQuiver then
      let some v' ← withTransparency .all (unfoldDefinition? ar.back!)
        | return none
      let e' := mkAppN e.getAppFn (ar.set! (ar.size - 1) v')
      return some (← withReducible (whnf e'))
  return none

private meta def support_congr_core
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "support congruence depth exhausted"
  | fuel + 1, a, b => do
    let key := (← instantiateMVars a, ← instantiateMVars b)
    let previous ← cache.get
    if let some pf := previous[key]? then return pf
    let pf ← do
      let a := (← instantiateMVars a).headBeta.consumeMData
      let b := (← instantiateMVars b).headBeta.consumeMData
      if let .letE _ _ val body _ := a then
        return ← support_congr_core cache fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← support_congr_core cache fuel a (body.instantiate1 val)
      if a == b then return ← mkHEqRefl a
      if ← isProp (← inferType a) then
        return ← mkAppM ``support_proofs_heq #[a, b]
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← support_congr_core cache fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← support_congr_core cache fuel a val
      if a.isForall && b.isForall then
        unless a.bindingDomain! == b.bindingDomain! do
          throwError "forall domains differ: {a.bindingDomain!} versus {b.bindingDomain!}"
        return ← withLocalDeclD a.bindingName! a.bindingDomain! fun x => do
          let hp ← support_congr_core cache fuel
            (a.bindingBody!.instantiate1 x) (b.bindingBody!.instantiate1 x)
          let ep ← mkAppM ``eq_of_heq #[hp]
          let all ← mkLambdaFVars #[x] ep
          let hf ← mkAppM ``support_forall_congr #[all]
          mkAppM ``heq_of_eq #[hf]
      if a.isLambda && b.isLambda then
        unless a.bindingDomain! == b.bindingDomain! do
          throwError "lambda domains differ: {a.bindingDomain!} versus {b.bindingDomain!}"
        return ← withLocalDeclD a.bindingName! a.bindingDomain! fun x => do
          let hp ← support_congr_core cache fuel
            (a.bindingBody!.instantiate1 x) (b.bindingBody!.instantiate1 x)
          let all ← mkLambdaFVars #[x] hp
          withTransparency .all (mkAppM ``support_fun_heq #[a, b, all])
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← support_congr_core cache fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← support_congr_core cache fuel a (mkAppN bf.consumeMData b.getAppArgs)
      if af.isMVar || bf.isMVar then
        unless ← isDefEq a b do throwError "unresolved tensor parameter"
        return ← mkHEqRefl a
      if af.isConstOf ``Functor.obj && bf.isConstOf ``Functor.obj then
        let fa := a.getAppArgs[4]!
        let fb := b.getAppArgs[4]!
        let na := if fa.getAppFn.isConstOf ``Functor.obj then
          fa.getAppArgs[4]!.getAppFn.constName? else none
        let nb := if fb.getAppFn.isConstOf ``Functor.obj then
          fb.getAppArgs[4]!.getAppFn.constName? else none
        if na != nb then
          if let some a' ← support_reduce_obj a then
            return ← support_congr_core cache fuel a' b
          if let some b' ← support_reduce_obj b then
            return ← support_congr_core cache fuel a b'
      if af.isConstOf ``Functor.obj && a.getAppArgs.size == 6 then
        let ar := a.getAppArgs
        if ar[4]!.getAppFn.isConstOf ``Functor.comp then
          let fs := ar[4]!.getAppArgs
          let x ← mkAppM ``Functor.obj #[fs[fs.size - 2]!, ar[5]!]
          let y ← mkAppM ``Functor.obj #[fs.back!, x]
          return ← support_congr_core cache fuel y b
      if bf.isConstOf ``Functor.obj && b.getAppArgs.size == 6 then
        let ar := b.getAppArgs
        if ar[4]!.getAppFn.isConstOf ``Functor.comp then
          let fs := ar[4]!.getAppArgs
          let x ← mkAppM ``Functor.obj #[fs[fs.size - 2]!, ar[5]!]
          let y ← mkAppM ``Functor.obj #[fs.back!, x]
          return ← support_congr_core cache fuel a y
      if af.isConstOf ``DerivedCategoryModule then
        let some x ← withTransparency .all (unfoldDefinition? a)
          | throwError "cannot unfold the coefficient-category alias"
        return ← support_congr_core cache fuel x b
      if bf.isConstOf ``DerivedCategoryModule then
        let some x ← withTransparency .all (unfoldDefinition? b)
          | throwError "cannot unfold the coefficient-category alias"
        return ← support_congr_core cache fuel a x
      let sharedType := af.isConstOf ``DerivedCategory ||
        af.isConstOf ``instCategoryDerivedCategory || af.isConstOf ``Sheaf ||
        af.isConstOf ``CategoryTheory.ObjectProperty.FullSubcategory.category ||
        af.isConstOf ``Functor.category || af.isConstOf ``CategoryTheory.Functor ||
        af.isConstOf ``HasDerivedCategory.ofIsGrothendieckAbelian
      if sharedType then
        if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
      if let some a' ← support_reduce_quiver a then
        if a' != a then return ← support_congr_core cache fuel a' b
      if let some b' ← support_reduce_quiver b then
        if b' != b then return ← support_congr_core cache fuel a b'
      let sameHead ← if af == bf then pure true
        else if af.isConst && bf.isConst && af.constName! == bf.constName! then
          isDefEq af bf
        else pure false
      if sameHead && a.getAppArgs.size == b.getAppArgs.size then
        let argsA := a.getAppArgs
        let argsB := b.getAppArgs
        let ct ← mkHCongrWithArity a.getAppFn argsA.size
        let mut ps := #[]
        for i in [:argsA.size] do
          let mut hp ← try
            support_congr_core cache fuel argsA[i]! argsB[i]!
          catch ex =>
            if af.isConstOf ``Functor.obj && i == 0 then
              throwError "object functors ({argsA.size}, {argsB.size}): \
                {argsA[argsA.size - 2]!} versus {argsB[argsB.size - 2]!}; {ex.toMessageData}"
            throwError "at {a.getAppFn} argument {i}: {ex.toMessageData}"
          if ct.argKinds[i]! == .eq then hp ← mkAppM ``eq_of_heq #[hp]
          ps := ps ++ #[argsA[i]!, argsB[i]!, hp]
        let pf := mkAppN ct.proof ps
        if (← inferType pf).isHEq then return pf
        else return ← mkAppM ``heq_of_eq #[pf]
      if af.isConstOf ``CommRing.toRing || bf.isConstOf ``CommRing.toRing then
        unless ← isDefEq a b do throwError "coefficient rings differ"
        return ← mkHEqRefl a
      if a.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory ||
          b.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
        unless ← isDefEq a b do throwError "coefficient braidings differ"
        return ← mkHEqRefl a
      if (← inferType a).consumeMData.getAppFn.isConstOf ``Quiver then
        if ← isDefEq a b then return ← mkHEqRefl a
      throwError "unmatched support data: {a} versus {b}"
    cache.modify (·.insert key pf)
    return pf

private meta def support_congr_heq (fuel : Nat) (a b : Expr) : MetaM Expr := do
  let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
  support_congr_core cache fuel a b

private meta def support_transport_local (userName : Name) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == userName)
      | throwError "no comparison named {userName}"
    let q ← support_congr_heq 500 target (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

end ProofTransport

/-- Tensor of two specified isomorphisms, constructed for a general bifunctor.
Source: the proper comparison tensor in the first coordinate calculation
(auxiliary; not a blueprint node). -/
def kunnethComparisonTensorIso {D : Type v} [Category.{u + 1} D]
    (T : D ⥤ D ⥤ D) {M M' N N' : D} (a : M ≅ M') (b : N ≅ N') :
    (T.obj M).obj N ≅ (T.obj M').obj N' :=
  (T.mapIso a).app N ≪≫ (T.obj M').mapIso b

variable (A : Type (u + 1)) [CommRing A] [Finite A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensorSymmetry supportedTensorSwapIso
  projectionMap properRouteProjection properRouteExchange
  rightDerivedLowerStarProjectionMap derivedBaseChangeMap
  rightDerivedLowerShriekBaseChangeMap kunnethMap

attribute [local implicit_reducible] derivedTensorRight
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  Compactification.ofIsPullback

section InputDefinition

attribute [local irreducible] rightDerivedLowerShriek

/-- Tensor of the two canonical proper forget-supports isomorphisms.
Source: the proper-support comparison in the first triangle of the blueprint
(auxiliary; not a blueprint node). -/
def properKunnethInput {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsProper f] [IsProper g] (E : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E)).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj K) ≅
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj E)).obj
        ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) :=
  kunnethComparisonTensorIso (derivedTensor (ModuleCat.{u + 1} A) S)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).app E)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) g).app K)

end InputDefinition

attribute [local irreducible] properKunnethInput

section CompactificationCalculation

attribute [local implicit_reducible] rightDerivedLowerShriek

omit [Finite A] in
private theorem proper_comparison_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (E : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app E =
      (lowerStar (ModuleCat.{u + 1} A)
        (HasCompactification.compactification f).g).rightDerivedFunctor.map
          ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
            (HasCompactification.compactification f).i).app E) ≫
        (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f).i
          (HasCompactification.compactification f).g f
          (HasCompactification.compactification f).comm).app E := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq]
  rfl

private theorem exchange_supports_native {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app
            ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) =
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom.app E) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E := by
  let c := HasCompactification.compactification f
  rw [rightDerivedLowerShriekBaseChangeMap_eq]
  simp only [rightDerivedLowerShriekBaseChangeMap', rightDerivedLowerShriekIso,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Category.assoc, proper_comparison_app, Functor.map_comp]
  rw [rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar]
  exact rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar _
    sq.toCommSq c (c.ofIsPullback sq) _ (c.isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback c.g g).toCommSq E

end CompactificationCalculation

open Lean Meta Elab Tactic in
private theorem exchange_supports {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) :
    (properRouteExchange A sq E).hom ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app
            ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) =
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom.app E) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E := by
  rw [properRouteExchange_hom]
  have hNative := exchange_supports_native A sq E
  dsimp only [rightDerivedLowerShriek, Functor.comp_obj] at hNative ⊢
  run_tac withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `hNative)
      | throwError "no native comparison"
    let q ← support_congr_heq 500 t (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

section ProjectionBridge

open Lean Meta Elab Tactic

attribute [local irreducible] derivedTensor

private theorem projection_supports {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (properRouteProjection A f E K).hom ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) f).hom.app
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).obj
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) f).hom.app E)).app K ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app E).app K := by
  rw [properRouteProjection_hom]
  have hNative := projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) f E K
  dsimp only [rightDerivedLowerShriek, derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    derivedTensorRightDerivedLowerStar, rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
    Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj] at hNative ⊢
  run_tac withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `hNative)
      | throwError "no native comparison"
    let q ← support_congr_heq 500 t (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

end ProjectionBridge

attribute [local irreducible] rightDerivedLowerShriek

section InnerCalculation

open Lean Meta Elab Tactic

attribute [local irreducible] derivedTensor

private theorem inner_supports {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (properSupportedKunnethInner A sq E K).inv ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app
            (((derivedTensor (ModuleCat.{u + 1} A) W).obj
              ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
                ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) f).hom.app E)) ≫
        (supportedTensorSwapIso (ModuleCat.{u + 1} A) Y
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
            ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj E)) K).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E)).app K ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).app K := by
  rw [properSupportedKunnethInner_inv]
  simp only [Category.assoc]
  have hAlgebra := inner_supports_algebra (derivedTensor (ModuleCat.{u + 1} A) Y)
    (supportedTensorSwapIso (ModuleCat.{u + 1} A) Y)
    (supportedTensorSwapIso_inv_naturality_left (ModuleCat.{u + 1} A) Y)
    (K := K)
    (Z := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E))
    (Z' := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj E))
    (properRouteExchange A sq E).hom
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q).hom.app _)
    ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) f).hom.app E))
    ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E)
    ((properRouteProjection A q
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) K).hom ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app _)
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).app K)
    (projection_supports A q
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) K)
    (exchange_supports A sq E)
  simpa only [Category.assoc, Functor.comp_obj] using hAlgebra

end InnerCalculation

attribute [local irreducible] derivedTensor properRouteCompIso
  rightDerivedLowerStarCompIsoOfComp rightDerivedLowerShriekIsoRightDerivedLowerStar

open Lean Meta Elab Tactic

/-- One relative Kunneth route agrees with the ordinary external product under proper
forget supports. This is a normalization of one route, for arbitrary proper factors.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first triangle, the
canonical pullback-counit computation; Stacks Tags 07A7, 0B56 and 0D6E
(auxiliary; not a blueprint node).

Proof: expand properSupportedKunnethRoute inverse. Replace its two forward
compact-support projection maps by ordinary projection maps using
projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar. The two
symmetries commute with the proper comparisons by naturality. For the exchange,
expand the chosen compactification into its open and proper factors. Naturality
of the open forget-supports adjunct and the open-unit cancellation identify the
supported exchange followed by forget supports with ordinary exchange after
pullback of forget supports. Independence under compactification refinements
allows the chosen compactification on the other side of the square. Expand the
specified supported compositor: the same open/proper comparison and the composite
counit formula identify it with the ordinary direct-image compositor. The resulting
forward path is the ordinary projection, tensor exchange, ordered projection and
ordinary compositor. By kunnethMap_eq_of_isPullback and tensor naturality this is
the ordinary Kunneth map with its factors reversed and its two outside braidings.
The braided pullback tensor comparison, or equivalently the common mixed-counit
transpose, puts the factors back in the order E,K and yields the displayed map.
This calculation uses no relation between E and K and compares only one route;
it does not assert equality of the two supported coordinate extractions. -/
theorem properRelativeKunneth_comp_forgetSupports {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [IsProper f] [IsProper g] [IsProper q] [IsProper h]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (properSupportedKunnethRoute A sq h w E K).inv ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) h).hom.app
          (((derivedTensor (ModuleCat.{u + 1} A) W).obj
            ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
              ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) =
      (properKunnethInput A f g E K).hom ≫
        kunnethMap (ModuleCat.{u + 1} A) p q f g h (sq.w.trans w) w E K := by
  let C := ModuleCat.{u + 1} A
  let F := rightDerivedLowerShriek C g
  let G := (lowerStar C g).rightDerivedFunctor
  let eta := rightDerivedLowerShriekIsoRightDerivedLowerStar C g
  let a := (rightDerivedLowerShriekIsoRightDerivedLowerStar C f).hom.app E
  let b := eta.hom.app K
  let t := (supportedTensorSwapIso C Y
    ((upperStar C g).leftDerivedFunctor.obj
      ((lowerStar C f).rightDerivedFunctor.obj E)) K).inv ≫
    ((derivedTensor C Y).map ((derivedBaseChangeMap C sq.toCommSq).app E)).app K ≫
    ((rightDerivedLowerStarProjectionMap C q).app
      ((upperStar C p).leftDerivedFunctor.obj E)).app K
  have hTensor := tensor_inputs_swap_algebra (derivedTensor C S)
    (supportedTensorSwapIso C S)
    (supportedTensorSwapIso_inv_naturality_left C S)
    (supportedTensorSwapIso_inv_naturality_right C S) a b
  have hInput :
      (supportedTensorSwapIso C S (F.obj K)
        ((rightDerivedLowerShriek C f).obj E)).inv ≫
        ((derivedTensor C S).map b).app ((rightDerivedLowerShriek C f).obj E) ≫
        ((derivedTensor C S).obj (G.obj K)).map a =
      (properKunnethInput A f g E K).hom ≫
        (supportedTensorSwapIso C S (G.obj K)
          ((lowerStar C f).rightDerivedFunctor.obj E)).inv := by
    simp only [properKunnethInput, kunnethComparisonTensorIso, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    run_tac support_transport_local `hTensor
  have hAlgebra := properKunnethNormalizationAlgebra F G eta.hom
    (supportedTensorSwapIso C S (F.obj K)
      ((rightDerivedLowerShriek C f).obj E)).inv
    (properRouteProjection A g K ((rightDerivedLowerShriek C f).obj E)).hom
    (properSupportedKunnethInner A sq E K).inv
    ((properRouteCompIso A q g h w).inv.app _)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar C h).hom.app _)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar C q).hom.app _)
    ((rightDerivedLowerStarCompIsoOfComp C q g h w).hom.app _)
    (((derivedTensor C Y).obj K).map ((upperStar C g).leftDerivedFunctor.map a))
    t
    (((derivedTensor C S).map b).app ((rightDerivedLowerShriek C f).obj E))
    (((rightDerivedLowerStarProjectionMap C g).app K).app
      ((rightDerivedLowerShriek C f).obj E))
    (((derivedTensor C S).obj (G.obj K)).map a)
    (((rightDerivedLowerStarProjectionMap C g).app K).app
      ((lowerStar C f).rightDerivedFunctor.obj E))
    (properKunnethInput A f g E K).hom
    (supportedTensorSwapIso C S (G.obj K)
      ((lowerStar C f).rightDerivedFunctor.obj E)).inv
    (kunnethMap C p q f g h (sq.w.trans w) w E K)
    (by
      have hc := properShriekComp_comp_forgetSupports A q g h w
        (((derivedTensor C W).obj
          ((upperStar C p).leftDerivedFunctor.obj E)).obj
            ((upperStar C q).leftDerivedFunctor.obj K))
      run_tac support_transport_local `hc)
    (by
      have hi := inner_supports A sq E K
      run_tac support_transport_local `hi)
    (by
      have hp := projection_supports A g K ((rightDerivedLowerShriek C f).obj E)
      run_tac support_transport_local `hp)
    (by
      have hn := (kunnethProjection_naturality_right C g K a).symm
      dsimp only [derivedTensorRightDerivedLowerStar,
        rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar,
        Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
        Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
        catToReflQuiver] at hn ⊢
      run_tac support_transport_local `hn)
    (by
      run_tac support_transport_local `hInput)
    (by
      have hk :=
        (kunnethMap_symmetricFactorization C p q f g h (sq.w.trans w) w E K).symm
      dsimp only [t, derivedTensorRightDerivedLowerStar,
        rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar,
        Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
        Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
        catToReflQuiver] at hk ⊢
      run_tac support_transport_local `hk)
  simp only [Category.assoc] at hAlgebra
  simp only [properSupportedKunnethRoute_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  run_tac support_transport_local `hAlgebra

end AlgebraicGeometry.Etale
