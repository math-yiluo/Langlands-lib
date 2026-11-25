/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import WeilConjectures.AlgebraicGeometry.EtaleKunnethTensorSymmetry
import WeilConjectures.AlgebraicGeometry.ProperRelativeKunnethSupports
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric

/-! # First coordinate extraction before a trace

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first triangle, coordinate interchange.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

set_option Elab.async false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SupportedTrace

section ProjectionComponents

variable (A : Type (u + 1)) [CommRing A] [Finite A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem projection_right_component {Z X : Scheme.{u}} (g : Z ⟶ X)
    [HasCompactification g] (E : DerivedCategoryModule A Z)
    (M : DerivedCategoryModule A X) :
    (projectionRightIso A g M).app E = (projectionIso A g E).app M := by
  apply Iso.ext
  rfl

end ProjectionComponents

attribute [local instance high] SymmetricCategory.toBraidedCategory

section General

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

private theorem native_swap_inverse (Z : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)) :
    (supportedTensorSwapIso C Z M N).inv = (supportedTensorSwapIso C Z N M).hom := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf Z.smallEtaleTopology C)
  exact (SymmetricCategory.braiding_swap_eq_inv_braiding M N).symm

private theorem native_swap_twice (Z : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)) :
    (supportedTensorSwapIso C Z M N).hom ≫
        (supportedTensorSwapIso C Z N M).hom = 𝟙 _ := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf Z.smallEtaleTopology C)
  exact SymmetricCategory.symmetry M N

private theorem tensor_iso_swap (Z : Scheme.{u})
    {M M' N N' : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)}
    (a : M ≅ M') (b : N ≅ N') :
    (((derivedTensor C Z).mapIso a).app N ≪≫
      ((derivedTensor C Z).obj M').mapIso b).hom ≫
        (supportedTensorSwapIso C Z M' N').hom =
      (supportedTensorSwapIso C Z M N).hom ≫
        (((derivedTensor C Z).mapIso b).app M ≪≫
          ((derivedTensor C Z).obj N').mapIso a).hom := by
  have hL := NatTrans.naturality_app (derivedTensorSymmetry C Z).hom N a.hom
  have hR := ((derivedTensorSymmetry C Z).hom.app M').naturality b.hom
  simp only [Functor.flip_obj_obj, Functor.flip_map_app, Functor.flip_obj_map] at hL hR
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    supportedTensorSwapIso, Category.assoc]
  rw [hR, ← Category.assoc, hL, Category.assoc,
    ((derivedTensor C Z).map b.hom).naturality a.hom]

end General

-- Congruence compares construction data without unfolding derived functors.
-- Proof fields are irrelevant even when their propositions have different expressions.
-- The kernel checks the generated equalities, including the coefficient braiding equality.
section ProofTransport

open Lean Meta Elab Tactic

private theorem coordinate_proofs_heq {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  have h : P = Q := propext ⟨fun _ ↦ q, fun _ ↦ p⟩
  cases h
  rfl

private theorem coordinate_forall_congr {D : Sort*} {p q : D → Prop}
    (h : ∀ x, p x = q x) : (∀ x, p x) = (∀ x, q x) :=
  congrArg (fun r : D → Prop ↦ ∀ x, r x) (funext h)

private theorem coordinate_fun_heq {D : Sort v} {E E' : D → Sort u}
    (f : ∀ x, E x) (g : ∀ x, E' x) (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  have he : E = E' := funext fun x ↦ type_eq_of_heq (h x)
  cases he
  exact heq_of_eq (funext fun x ↦ eq_of_heq (h x))

private meta def coordinate_reduce_obj (e : Expr) : MetaM (Option Expr) := do
  unless e.getAppFn.isConstOf ``Functor.obj && e.getAppArgs.size == 6 do return none
  let f := e.getAppArgs[4]!
  if f.getAppFn.isConstOf ``derivedTensorRight then
    -- Both tensor wrappers have the same parameters, followed by the fixed object.
    let ar := f.getAppArgs
    let t := mkAppN (mkConst ``derivedTensor f.getAppFn.constLevels!) ar.pop
    let x ← mkAppM ``Functor.obj #[t, e.getAppArgs[5]!]
    return some (← mkAppM ``Functor.obj #[x, ar.back!])
  unless f.getAppFn.isConstOf ``Functor.obj && f.getAppArgs.size == 6 do return none
  let tf := f.getAppArgs[4]!
  if tf.getAppFn.isConstOf ``Functor.flip then
    let x ← mkAppM ``Functor.obj #[tf.getAppArgs.back!, e.getAppArgs[5]!]
    return some (← mkAppM ``Functor.obj #[x, f.getAppArgs[5]!])
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

private meta def coordinate_congr_core
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
        return ← coordinate_congr_core cache fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← coordinate_congr_core cache fuel a (body.instantiate1 val)
      if a == b then return ← mkHEqRefl a
      if ← isProp (← inferType a) then
        return ← mkAppM ``coordinate_proofs_heq #[a, b]
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← coordinate_congr_core cache fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← coordinate_congr_core cache fuel a val
      if a.isForall && b.isForall then
        unless a.bindingDomain! == b.bindingDomain! do
          throwError "forall domains differ: {a.bindingDomain!} versus {b.bindingDomain!}"
        return ← withLocalDeclD a.bindingName! a.bindingDomain! fun x => do
          let hp ← coordinate_congr_core cache fuel
            (a.bindingBody!.instantiate1 x) (b.bindingBody!.instantiate1 x)
          let ep ← mkAppM ``eq_of_heq #[hp]
          let all ← mkLambdaFVars #[x] ep
          let hf ← mkAppM ``coordinate_forall_congr #[all]
          mkAppM ``heq_of_eq #[hf]
      if a.isLambda && b.isLambda then
        unless a.bindingDomain! == b.bindingDomain! do
          throwError "lambda domains differ: {a.bindingDomain!} versus {b.bindingDomain!}"
        return ← withLocalDeclD a.bindingName! a.bindingDomain! fun x => do
          let hp ← coordinate_congr_core cache fuel
            (a.bindingBody!.instantiate1 x) (b.bindingBody!.instantiate1 x)
          let all ← mkLambdaFVars #[x] hp
          withTransparency .all (mkAppM ``coordinate_fun_heq #[a, b, all])
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← coordinate_congr_core cache fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← coordinate_congr_core cache fuel a (mkAppN bf.consumeMData b.getAppArgs)
      if af.isMVar || bf.isMVar then
        unless ← isDefEq a b do throwError "unresolved tensor parameter"
        return ← mkHEqRefl a
      if let .proj n i f := af then
        if n == ``CategoryTheory.Functor && i == 0 && a.getAppArgs.size == 1 then
          let x ← mkAppM ``Functor.obj #[f, a.getAppArgs[0]!]
          return ← coordinate_congr_core cache fuel x b
      if let .proj n i f := bf then
        if n == ``CategoryTheory.Functor && i == 0 && b.getAppArgs.size == 1 then
          let x ← mkAppM ``Functor.obj #[f, b.getAppArgs[0]!]
          return ← coordinate_congr_core cache fuel a x
      if af.isConstOf ``Functor.obj && bf.isConstOf ``Functor.obj then
        let fa := a.getAppArgs[4]!
        let fb := b.getAppArgs[4]!
        let wrapper (f : Expr) :=
          f.getAppFn.isConstOf ``rightDerivedLowerShriek ||
            f.getAppFn.isConstOf ``rightDerivedLowerShriekOfCompactification
        if fa.getAppFn != fb.getAppFn then
          if wrapper fa then
            let some f ← withTransparency .all (unfoldDefinition? fa)
              | throwError "cannot expand a supported image object"
            let x ← mkAppM ``Functor.obj #[f, a.getAppArgs[5]!]
            return ← coordinate_congr_core cache fuel x b
          if wrapper fb then
            let some f ← withTransparency .all (unfoldDefinition? fb)
              | throwError "cannot expand a supported image object"
            let x ← mkAppM ``Functor.obj #[f, b.getAppArgs[5]!]
            return ← coordinate_congr_core cache fuel a x
      if af.isConstOf ``Functor.obj && bf.isConstOf ``Functor.obj then
        let fa := a.getAppArgs[4]!
        let fb := b.getAppArgs[4]!
        let na := if fa.getAppFn.isConstOf ``Functor.obj then
          fa.getAppArgs[4]!.getAppFn.constName? else none
        let nb := if fb.getAppFn.isConstOf ``Functor.obj then
          fb.getAppArgs[4]!.getAppFn.constName? else none
        if na != nb then
          if let some a' ← coordinate_reduce_obj a then
            return ← coordinate_congr_core cache fuel a' b
          if let some b' ← coordinate_reduce_obj b then
            return ← coordinate_congr_core cache fuel a b'
      if af.isConstOf ``Functor.obj && a.getAppArgs.size == 6 then
        let ar := a.getAppArgs
        if ar[4]!.getAppFn.isConstOf ``Functor.comp then
          let fs := ar[4]!.getAppArgs
          let x ← mkAppM ``Functor.obj #[fs[fs.size - 2]!, ar[5]!]
          let y ← mkAppM ``Functor.obj #[fs.back!, x]
          return ← coordinate_congr_core cache fuel y b
      if bf.isConstOf ``Functor.obj && b.getAppArgs.size == 6 then
        let ar := b.getAppArgs
        if ar[4]!.getAppFn.isConstOf ``Functor.comp then
          let fs := ar[4]!.getAppArgs
          let x ← mkAppM ``Functor.obj #[fs[fs.size - 2]!, ar[5]!]
          let y ← mkAppM ``Functor.obj #[fs.back!, x]
          return ← coordinate_congr_core cache fuel a y
      if af.isConstOf ``Iso.hom then
        let i := a.getAppArgs.back!
        if i.getAppFn.isConstOf ``Iso.symm then
          let x ← mkAppM ``Iso.inv #[i.getAppArgs.back!]
          return ← coordinate_congr_core cache fuel x b
      if bf.isConstOf ``Iso.hom then
        let i := b.getAppArgs.back!
        if i.getAppFn.isConstOf ``Iso.symm then
          let x ← mkAppM ``Iso.inv #[i.getAppArgs.back!]
          return ← coordinate_congr_core cache fuel a x
      if af.isConstOf ``Iso.inv then
        let i := a.getAppArgs.back!
        if i.getAppFn.isConstOf ``Iso.app then
          let ar := i.getAppArgs
          let j ← mkAppM ``Iso.inv #[ar[ar.size - 2]!]
          let x ← mkAppM ``NatTrans.app #[j, ar.back!]
          return ← coordinate_congr_core cache fuel x b
      if bf.isConstOf ``Iso.inv then
        let i := b.getAppArgs.back!
        if i.getAppFn.isConstOf ``Iso.app then
          let ar := i.getAppArgs
          let j ← mkAppM ``Iso.inv #[ar[ar.size - 2]!]
          let x ← mkAppM ``NatTrans.app #[j, ar.back!]
          return ← coordinate_congr_core cache fuel a x
      if af.isConstOf ``Functor.comp then
        let ar := a.getAppArgs
        let f := ar[ar.size - 2]!
        if f.getAppFn.isConstOf ``Functor.comp then
          let fs := f.getAppArgs
          let gh ← mkAppM ``Functor.comp #[fs.back!, ar.back!]
          let x ← mkAppM ``Functor.comp #[fs[fs.size - 2]!, gh]
          return ← coordinate_congr_core cache fuel x b
      if bf.isConstOf ``Functor.comp then
        let ar := b.getAppArgs
        let f := ar[ar.size - 2]!
        if f.getAppFn.isConstOf ``Functor.comp then
          let fs := f.getAppArgs
          let gh ← mkAppM ``Functor.comp #[fs.back!, ar.back!]
          let x ← mkAppM ``Functor.comp #[fs[fs.size - 2]!, gh]
          return ← coordinate_congr_core cache fuel a x
      if af.isConstOf ``rightDerivedLowerShriek then
        let some x ← withTransparency .all (unfoldDefinition? a)
          | throwError "cannot unfold the supported direct-image wrapper"
        return ← coordinate_congr_core cache fuel x b
      if bf.isConstOf ``rightDerivedLowerShriek then
        let some x ← withTransparency .all (unfoldDefinition? b)
          | throwError "cannot unfold the supported direct-image wrapper"
        return ← coordinate_congr_core cache fuel a x
      let aliasData (x : Expr) :=
        x.getAppFn.isConstOf ``derivedTensorRight ||
        x.getAppFn.isConstOf ``derivedTensorRightFunctor ||
        x.getAppFn.isConstOf ``CoordinateTrace.pull ||
        x.getAppFn.isConstOf ``CoordinateTrace.push ||
        x.getAppFn.isConstOf ``CoordinateTrace.tensor ||
        x.getAppFn.isConstOf ``push ||
        x.getAppFn.isConstOf ``DerivedCategoryModule
      if af != bf then
        if aliasData a then
          let some x ← withTransparency .all (unfoldDefinition? a)
            | throwError "cannot unfold a coordinate alias"
          return ← coordinate_congr_core cache fuel x b
        if aliasData b then
          let some x ← withTransparency .all (unfoldDefinition? b)
            | throwError "cannot unfold a coordinate alias"
          return ← coordinate_congr_core cache fuel a x
      let sharedType := af.isConstOf ``DerivedCategory ||
        af.isConstOf ``instCategoryDerivedCategory || af.isConstOf ``Sheaf ||
        af.isConstOf ``CategoryTheory.ObjectProperty.FullSubcategory.category ||
        af.isConstOf ``Functor.category || af.isConstOf ``CategoryTheory.Functor ||
        af.isConstOf ``HasDerivedCategory.ofIsGrothendieckAbelian
      if sharedType then
        if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
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
            coordinate_congr_core cache fuel argsA[i]! argsB[i]!
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

private meta def coordinate_congr_heq (fuel : Nat) (a b : Expr) : MetaM Expr := do
  let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
  coordinate_congr_core cache fuel a b

end ProofTransport

variable (A : Type (u + 1)) [CommRing A] [Finite A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  rightDerivedLowerShriek derivedTensor derivedTensorSymmetry

attribute [local implicit_reducible] derivedTensorRight

omit [Finite A] in
private theorem proper_input_swap {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsProper f] [IsProper g] (E : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) :
    (properKunnethInput A f g E K).hom ≫
        (supportedTensorSwapIso (ModuleCat.{u + 1} A) S
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj E)
          ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K)).hom =
      (supportedTensorSwapIso (ModuleCat.{u + 1} A) S
        ((push A f).obj E) ((push A g).obj K)).hom ≫
          (properKunnethInput A g f K E).hom := by
  exact tensor_iso_swap (ModuleCat.{u + 1} A) S
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).app E)
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) g).app K)

section RelativeCalculus

attribute [local irreducible] properKunnethInput kunnethMap
  rightDerivedLowerStarCompIsoOfComp properSupportedKunnethRoute
  properSupportedKunnethInner supportedTensorSwapIso
  derivedBaseChangeMap rightDerivedLowerStarProjectionMap

private theorem relative_symmetry {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [IsProper f] [IsProper g] [IsProper p] [IsProper q] [IsProper h]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (properSupportedKunnethRoute A sq h w E K).hom ≫
        (supportedTensorSwapIso (ModuleCat.{u + 1} A) S
          ((push A f).obj E) ((push A g).obj K)).hom =
      (push A h).map
        (supportedTensorSwapIso (ModuleCat.{u + 1} A) W
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)
          ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)).hom ≫
        (properSupportedKunnethRoute A sq.flip h (sq.w.trans w) K E).hom := by
  let r := properSupportedKunnethRoute A sq h w E K
  let r' := properSupportedKunnethRoute A sq.flip h (sq.w.trans w) K E
  let sw := supportedTensorSwapIso (ModuleCat.{u + 1} A) W
    ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)
          ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)
  let ss := supportedTensorSwapIso (ModuleCat.{u + 1} A) S
    ((push A f).obj E) ((push A g).obj K)
  let c := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) h
  have hi : r.inv ≫ (push A h).map sw.hom = ss.hom ≫ r'.inv := by
    apply (cancel_mono (c.hom.app _)).1
    simp only [Category.assoc]
    rw [c.hom.naturality sw.hom]
    change r.inv ≫ c.hom.app _ ≫ _ = ss.hom ≫ r'.inv ≫ c.hom.app _
    rw [← Category.assoc,
      properRelativeKunneth_comp_forgetSupports A sq h w E K]
    rw [Category.assoc, kunnethMap_tensorSymmetry]
    rw [← Category.assoc, proper_input_swap, Category.assoc]
    rw [properRelativeKunneth_comp_forgetSupports A sq.flip h (sq.w.trans w) K E]
  change r.hom ≫ ss.hom = (push A h).map sw.hom ≫ r'.hom
  apply (cancel_epi r.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hi]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local instance 200000] ModuleCat.MonoidalCategory.instBraidedCategory

private abbrev nativeProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (E : DerivedCategoryModule A X)
    (M : DerivedCategoryModule A Y) := (projectionIso A f E).app M

private def nativeExchange {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  (asIso (rightDerivedLowerShriekBaseChangeMap A sq)).app E

private def nativeInner {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :=
  (nativeProjection A q ((CoordinateTrace.pull A p).obj E) K).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).mapIso
      (nativeExchange A sq E).symm).app K ≪≫
    CoordinateTrace.swap A Y ((CoordinateTrace.pull A g).obj ((push A f).obj E)) K

private def nativeRoute {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [IsProper f] [IsProper g] [IsProper q] [IsProper h]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :=
  (properRouteCompIso A q g h w).app
      (CoordinateTrace.tensor A W
        ((CoordinateTrace.pull A p).obj E) ((CoordinateTrace.pull A q).obj K)) ≪≫
    (push A g).mapIso (nativeInner A sq E K) ≪≫
    (nativeProjection A g K ((push A f).obj E)).symm ≪≫
    CoordinateTrace.swap A S ((push A g).obj K) ((push A f).obj E)

open Lean Meta Elab Tactic in
private theorem native_relative_symmetry {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [IsProper f] [IsProper g] [IsProper p] [IsProper q] [IsProper h]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (nativeRoute A sq h w E K).hom ≫
        (CoordinateTrace.swap A S ((push A f).obj E) ((push A g).obj K)).hom =
      (push A h).map
        (CoordinateTrace.swap A W
          ((CoordinateTrace.pull A p).obj E) ((CoordinateTrace.pull A q).obj K)).hom ≫
        (nativeRoute A sq.flip h (sq.w.trans w) K E).hom := by
  have hs := relative_symmetry A sq h w E K
  simp only [nativeRoute, properSupportedKunnethRoute, nativeInner,
    properSupportedKunnethInner, nativeProjection, properRouteProjection,
    nativeExchange, properRouteExchange, projectionIso, CoordinateTrace.swap,
    supportedTensorSwapIso, CoordinateTrace.pull, CoordinateTrace.tensor,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.comp_obj, Category.assoc] at hs ⊢
  dsimp only [push, rightDerivedLowerShriek, derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    derivedTensorRightDerivedLowerStar, rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
    Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
    ModuleCat.MonoidalCategory.symmetricCategory, SymmetricCategory.ofFaithful] at hs ⊢
  run_tac withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `hs)
      | throwError "no relative symmetry calculation"
    let q ← coordinate_congr_heq 500 t (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

end RelativeCalculus

attribute [local instance 200000] ModuleCat.MonoidalCategory.instBraidedCategory

omit [Finite A] in
private theorem swap_swap (Z : Scheme.{u}) (M N : DerivedCategoryModule A Z) :
    (CoordinateTrace.swap A Z M N).hom ≫ (CoordinateTrace.swap A Z N M).hom = 𝟙 _ := by
  simpa only [CoordinateTrace.swap, supportedTensorSwapIso] using
    native_swap_twice (ModuleCat.{u + 1} A) Z M N

open Lean Meta Elab Tactic

attribute [local irreducible] projectionMap rightDerivedLowerShriekBaseChangeMap

private theorem inner_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M B : DerivedCategoryModule A X) :
    (nativeInner A (IsPullback.of_hasPullback f f) M B).hom =
      (comparison A f B M).hom := by
  have hp : (projectionRightIso A (pullback.snd f f) B).inv.app
        ((CoordinateTrace.pull A (pullback.fst f f)).obj M) =
      (projectionIso A (pullback.snd f f)
        ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).inv.app B := by
    simpa only [Iso.app_inv] using congrArg Iso.inv
      (projection_right_component A (pullback.snd f f)
        ((CoordinateTrace.pull A (pullback.fst f f)).obj M) B)
  have he : (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app M =
      (nativeExchange A (IsPullback.of_hasPullback f f) M).inv := by
    simp only [TraceDiagonalDatum.baseChangeIso, nativeExchange, Iso.app_inv]
  simp only [nativeInner, comparison, comparisonIso,
    TraceDiagonalDatum.sndProjectionIso, nativeProjection, Iso.app_hom, Iso.app_inv,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc,
    derivedTensorRight, Functor.flip_obj_map, CoordinateTrace.swap, Iso.app_inv]
  have hs := native_swap_inverse (ModuleCat.{u + 1} A) X B
    ((CoordinateTrace.pull A f).obj ((push A f).obj M))
  simp only [supportedTensorSwapIso, Iso.app_inv, Iso.app_hom] at hs
  have hm := congrArg
    (fun z ↦ ((derivedTensor (ModuleCat.{u + 1} A) X).map z).app B) he.symm
  run_tac withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some (_, lhs, rhs) := target.consumeMData.eq?
      | throwError "expected an inner comparison equation"
    let parts := fun (e : Expr) => Id.run do
      let ar := e.getAppArgs
      let br := ar.back!.getAppArgs
      return #[ar[ar.size - 2]!, br[br.size - 2]!, br.back!]
    let ls := parts lhs
    let rs := parts rhs
    let ds := (← getLCtx).decls.toList.filterMap id
    let mut proofs := #[]
    for n in #[`hp, `hm, `hs] do
      let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == n)
        | throwError "missing component {n}"
      let h ← if n == `hm then pure d.toExpr else mkAppM ``Eq.symm #[d.toExpr]
      proofs := proofs.push h
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
    for i in [:3] do
      let component ← mkEq ls[i]! rs[i]!
      let q ← try
        coordinate_congr_heq 500 component (← inferType proofs[i]!)
      catch ex => throwError "inner component {i}: {ex.toMessageData}"
      let e ← mkAppM ``eq_of_heq #[q]
      let h ← mkAppM ``Eq.mpr #[e, proofs[i]!]
      let hh ← mkAppM ``heq_of_eq #[h]
      cache.modify (·.insert (ls[i]!, rs[i]!) hh)
    let h ← coordinate_congr_core cache 500 lhs rhs
    (← getMainGoal).assign (← mkAppM ``eq_of_heq #[h])

private theorem ordered_inverse_exchange {X Y : Scheme.{u}} (p : X ⟶ Y)
    [HasCompactification p] (M Z : DerivedCategoryModule A Y)
    (E : DerivedCategoryModule A X)
    (e : Z ≅ (push A p).obj E) :
    (push A p).map (CoordinateTrace.swap A X
      ((CoordinateTrace.pull A p).obj M) E).hom ≫
        (projectionIso A p E).inv.app M ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map e.inv).app M ≫
        (CoordinateTrace.swap A Y Z M).hom =
      (orderedProjection A p M E).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).obj M).map e.inv := by
  have hx := native_swap_inverse (ModuleCat.{u + 1} A) X E
    ((CoordinateTrace.pull A p).obj M)
  have hy := native_swap_inverse (ModuleCat.{u + 1} A) Y M ((push A p).obj E)
  have hn := supportedTensorSwapIso_hom_naturality_left
    (ModuleCat.{u + 1} A) Y e.inv M
  simp only [supportedTensorSwapIso, Iso.app_inv, Iso.app_hom] at hx hy hn
  simp only [orderedProjection, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    CoordinateTrace.swap, Iso.app_hom, Category.assoc]
  rw [hx, hy, hn]

private theorem inner_first {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M B : DerivedCategoryModule A X) :
    (push A (pullback.fst f f)).map
        (CoordinateTrace.swap A (pullback f f)
          ((CoordinateTrace.pull A (pullback.fst f f)).obj M)
          ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).hom ≫
        (nativeInner A (IsPullback.of_hasPullback f f).flip B M).hom =
      (orderedProjection A (pullback.fst f f) M
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((SfDiagonalKernel.exchangeFirst A f).inv.app B) := by
  have hh := ordered_inverse_exchange A (pullback.fst f f) M
        ((CoordinateTrace.pull A f).obj ((push A f).obj B))
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B)
        ((SfDiagonalKernel.exchangeFirst A f).app B)
  simp only [nativeInner, nativeProjection, nativeExchange,
    SfDiagonalKernel.exchangeFirst, CoordinateTrace.swap,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.comp_obj] at hh ⊢
  dsimp only [push, CoordinateTrace.push, CoordinateTrace.pull, CoordinateTrace.tensor,
    rightDerivedLowerShriek,
    rightDerivedLowerShriekOfCompactification, DerivedCategoryModule,
    Functor.comp_obj] at hh ⊢
  run_tac withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `hh)
      | throwError "no ordered inverse exchange equation"
    let q ← coordinate_congr_heq 500 t (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

private theorem comp_iso_eq {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S)
    (h : W ⟶ S) (w : p ≫ f = h) [IsProper p] [IsProper f] [IsProper h] :
    properRouteCompIso A p f h w =
      (rightDerivedLowerShriekCongrIso A w).symm ≪≫
        rightDerivedLowerShriekCompIso A p f := by
  rfl

private theorem comp_iso_refl {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S)
    [IsProper p] [IsProper f] :
    properRouteCompIso A p f (p ≫ f) rfl = rightDerivedLowerShriekCompIso A p f := by
  apply Iso.ext
  simp only [properRouteCompIso, rightDerivedLowerShriekCongrIso,
    Iso.trans_hom, Iso.symm_hom, Iso.refl_inv, Category.id_comp]

-- Use the component equations without expanding the constructions during rewriting.
attribute [local irreducible] properRouteCompIso rightDerivedLowerShriekCompIso
  rightDerivedLowerShriekCongrIso projectionIso projectionRightIso
  nativeInner nativeExchange nativeRoute comparison comparisonIso
  orderedProjection directComparison

/-- Interchange the two supported coordinate extractions before applying any trace.
Source: thm-amb-p1-adjunction.proof.md, first triangle, interchange of the two
coordinates (auxiliary; not a blueprint node).

Proof: construct the proper-supported Kunneth route from the specified compositor,
projection, exchange and tensor symmetry. Normalize its inverse to the ordinary
Kunneth map using the proper forget-supports comparisons. The ordinary Kunneth
map is symmetric: both orders have the same mixed-counit transpose, after the
braided pullback tensor comparison. Naturality of the tensor of the proper
comparisons therefore gives symmetry of the supported route, by cancellation.
For the self-product, its second-coordinate inner map is comparison: the reversed
inverse symmetry is the forward symmetry. Move the kernel swap through the
first compositor by naturality. The first-coordinate inner map following the
swap is orderedProjection inverse followed by inverse exchange, by naturality
and involutivity of symmetry. The second compositor followed by directComparison
is the first compositor, directly by their definitions. Cancel that compositor
and the two final swaps. This gives the displayed morphism equality for arbitrary
B and M. No trace, line condition, diagonal class or integral is used; empty
schemes and the zero coefficient ring satisfy the same canonical-mate identities. -/
theorem firstExtraction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (B M : DerivedCategoryModule A X) :
    (push A f).map (comparison A f B M).hom ≫
        (projectionIso A f B).inv.app ((push A f).obj M) =
      (directComparison A f).hom.app (kernel A f B M) ≫
        (push A f).map
          ((orderedProjection A (pullback.fst f f) M
              ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv ≫
            ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              ((SfDiagonalKernel.exchangeFirst A f).inv.app B)) ≫
        (projectionIso A f M).inv.app ((push A f).obj B) ≫
        (CoordinateTrace.swap A Y ((push A f).obj M) ((push A f).obj B)).hom := by
  let V := kernel A f B M
  let V' := CoordinateTrace.tensor A (pullback f f)
    ((CoordinateTrace.pull A (pullback.snd f f)).obj B)
    ((CoordinateTrace.pull A (pullback.fst f f)).obj M)
  let h := pullback.fst f f ≫ f
  let w := (pullback.condition (f := f) (g := f)).symm
  let c2 := properRouteCompIso A (pullback.snd f f) f h w
  let c1 := rightDerivedLowerShriekCompIso A (pullback.fst f f) f
  let sw := CoordinateTrace.swap A (pullback f f)
    ((CoordinateTrace.pull A (pullback.fst f f)).obj M)
    ((CoordinateTrace.pull A (pullback.snd f f)).obj B)
  have hc : c2.hom.app V ≫ (directComparison A f).hom.app V = c1.hom.app V := by
    simp only [c1, c2, comp_iso_eq, directComparison,
      Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app_assoc]
  have hs := native_relative_symmetry A (IsPullback.of_hasPullback f f) h w M B
  simp only [nativeRoute, nativeProjection, Iso.trans_hom, Iso.app_hom,
    Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] at hs
  have hf : properRouteCompIso A (pullback.fst f f) f h
      ((IsPullback.of_hasPullback f f).w.trans w) = c1 :=
    comp_iso_refl A (pullback.fst f f) f
  rw [hf] at hs
  change c2.hom.app V ≫ (push A f).map
      (nativeInner A (IsPullback.of_hasPullback f f) M B).hom ≫
      (projectionIso A f B).inv.app ((push A f).obj M) ≫
      (CoordinateTrace.swap A Y ((push A f).obj B) ((push A f).obj M)).hom ≫
      (CoordinateTrace.swap A Y ((push A f).obj M) ((push A f).obj B)).hom =
    (push A h).map sw.hom ≫ c1.hom.app V' ≫ (push A f).map
      (nativeInner A (IsPullback.of_hasPullback f f).flip B M).hom ≫
      (projectionIso A f M).inv.app ((push A f).obj B) ≫
      (CoordinateTrace.swap A Y ((push A f).obj M) ((push A f).obj B)).hom at hs
  rw [swap_swap, Category.comp_id, inner_comparison] at hs
  rw [reassoc_of% (c1.hom.naturality sw.hom)] at hs
  rw [← Functor.map_comp_assoc, inner_first] at hs
  apply (cancel_epi (c2.hom.app V)).1
  rw [reassoc_of% hc]
  exact hs

end AlgebraicGeometry.Etale.SupportedTrace
