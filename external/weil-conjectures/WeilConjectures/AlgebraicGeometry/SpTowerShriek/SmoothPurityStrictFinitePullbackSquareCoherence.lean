/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicConjugateComparisonTransport
/-! # Fixed-scalar coherence of the pullback-square comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
attribute [local instance 30000] SheafOfModules.instAbelian
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
attribute [local irreducible] sfIntrinsicModuleEquivalence
  Functor.mapDerivedCategory Functor.rightDerivedFunctor HasDerivedCategory.standard
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.ProEt
  CategoryTheory.MorphismProperty
  proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
-- Produce explicit checked congruences for definitional instance diamonds.
-- Each reduction is recorded as a separate reflexivity theorem; the final
-- proof uses these equations, so the kernel never reduces the complete word.
-- Explicit comparison congruences are checked within this declaration.
private meta def conversionOfEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  unless ty.isEq do throwError "expected equality"
  return Lean.mkAppN (Lean.mkConst ``heq_of_eq ty.getAppFn.constLevels!)
    (ty.getAppArgs.push h)

-- Explicit comparison congruences are checked within this declaration.
private meta def conversionSymm (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.symm ty.getAppFn.constLevels!) #[α, β, a, b, h]

-- Explicit comparison congruences are checked within this declaration.
private meta def conversionTrans (h k : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  let some (_, _, γ, c) := (← Lean.Meta.inferType k).heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.trans ty.getAppFn.constLevels!)
    #[α, β, γ, a, b, c, h, k]

-- Explicit comparison congruences are checked within this declaration.
private meta def conversionToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, _, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq ty.getAppFn.constLevels!) #[α, a, b, h]

-- Explicit comparison congruences are checked within this declaration.
private meta def conversionReduction (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let α ← Lean.Meta.inferType a
  let level ← Lean.Meta.getLevel α
  let type := Lean.mkApp3 (Lean.mkConst ``Eq [level]) α a b
  let value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [level]) α a
  let h ← Lean.Meta.mkAuxTheorem type value
    (zetaDelta := true) (kind? := `_finiteReduction)
  conversionOfEq h

-- Explicit comparison congruences are checked within this declaration.
private meta partial def conversionCongruence
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (congrCache : IO.Ref (Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem))
    (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← Lean.Meta.mkHEqRefl a
  if let some h := (← cache.get).get? (a, b) then return h
  let compute : Lean.MetaM Lean.Expr := do
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    let reduce (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
      if let .letE _ _ v body _ := e then return some (body.instantiate1 v)
      if e.getAppFn.isFVar then
        let decl ← e.getAppFn.fvarId!.getDecl
        if let some value := decl.value? then
          return some (Lean.mkAppN value e.getAppArgs)
      let projection ← match e.getAppFn with
        | .proj n i major => pure (some (n, i, major, e.getAppArgs))
        | .const name _ => do
          match (← Lean.getProjectionFnInfo? name) with
          | none => pure none
          | some info => do
            let args := e.getAppArgs
            if args.size < info.numParams + 1 then pure none else do
              let major := args[info.numParams]!
              let ty ← Lean.Meta.whnf (← Lean.Meta.inferType major)
              pure (some (ty.getAppFn.constName!, info.i, major,
                args.extract (info.numParams + 1) args.size))
        | _ => pure none
      if let some (n, i, major, args) := projection then
        let structural := #[``CategoryTheory.Iso.symm, ``CategoryTheory.Iso.trans,
          ``CategoryTheory.Functor.mapIso, ``CategoryTheory.Iso.app,
          ``CategoryTheory.Functor.comp, ``Compactification.ofIsPullback]
        if major.getAppFn.isConst && structural.contains major.getAppFn.constName! then
          if let some major' ← Lean.Meta.unfoldDefinition? major
              (ignoreTransparency := true) then
            let major' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf major')
            let field := Lean.Expr.proj n i major'
            let field := (← field.reduceProjStruct?).getD field
            return some (Lean.mkAppN field args).headBeta
      if let .proj n i major := e.getAppFn then
        let env ← Lean.getEnv
        let some info := Lean.getStructureInfo? env n | throwError "unknown structure {n}"
        let some proj := Lean.getProjFnForField? env n info.fieldNames[i]! |
          throwError "unknown projection of {n}"
        let majorType ← Lean.Meta.whnf (← Lean.Meta.inferType major)
        unless majorType.getAppFn.isConstOf n do
          throwError "unexpected projection type {majorType}"
        let head := Lean.mkAppN (Lean.mkConst proj majorType.getAppFn.constLevels!)
          (majorType.getAppArgs.push major)
        return some (Lean.mkAppN head e.getAppArgs)
      if e.headBeta != e then return some e.headBeta
      if let some e' ← e.reduceProjStruct? then return some e'
      return none
    if let some a' ← reduce a then
      return ← conversionTrans (← conversionReduction a a')
        (← conversionCongruence cache congrCache a' b)
    if let some b' ← reduce b then
      return ← conversionTrans (← conversionCongruence cache congrCache a b')
        (← conversionSymm (← conversionReduction b b'))
    let mut congruenceError : Option Lean.Exception := none
    let sameHead := a.getAppFn == b.getAppFn ||
      (a.getAppFn.isConst && b.getAppFn.isConst &&
        a.getAppFn.constName! == b.getAppFn.constName!)
    if sameHead && a.isApp && a.getAppNumArgs == b.getAppNumArgs then
      try
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let key := (a.getAppFn, aa.size)
        let ct ← match (← congrCache.get).get? key with
          | some ct => pure ct
          | none => do
            let ct ← if a.getAppFn.hasFVar then
                Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
              else Lean.Meta.withLCtx {} {} <|
                Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
            let proof ← Lean.Meta.mkAuxTheorem ct.type ct.proof
              (kind? := `_finiteCongruence)
            let ct := { ct with proof := proof }
            congrCache.modify fun m => m.insert key ct
            pure ct
        let mut args := #[]
        for i in [:aa.size] do
          let h ← conversionCongruence cache congrCache aa[i]! bb[i]!
          let h ← if ct.argKinds[i]! == .eq then conversionToEq h else pure h
          args := args ++ #[aa[i]!, bb[i]!, h]
        let h := Lean.mkAppN ct.proof args
        return ← if (← Lean.Meta.inferType h).isHEq then pure h else conversionOfEq h
      catch err => congruenceError := some err
    if (← Lean.Meta.isClass? (← Lean.Meta.inferType a)).isSome then
      return ← conversionReduction a b
    let a' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf a)
    let a' ← match (← reduce a') with
      | some v => pure v
      | none => pure a'
    if a' != a then
      return ← conversionTrans (← conversionReduction a a')
        (← conversionCongruence cache congrCache a' b)
    let b' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf b)
    let b' ← match (← reduce b') with
      | some v => pure v
      | none => pure b'
    if b' != b then
      return ← conversionTrans (← conversionCongruence cache congrCache a b')
        (← conversionSymm (← conversionReduction b b'))
    if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
      let a' ← match (← reduce a') with
        | some v => pure v
        | none => pure a'
      if a' != a then
        return ← conversionTrans (← conversionReduction a a')
          (← conversionCongruence cache congrCache a' b)
    if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
      let b' ← match (← reduce b') with
        | some v => pure v
        | none => pure b'
      if b' != b then
        return ← conversionTrans (← conversionCongruence cache congrCache a b')
          (← conversionSymm (← conversionReduction b b'))
    if a.isLambda && b.isLambda then return ← conversionReduction a b
    if let some err := congruenceError then throw err
    throwError "Unmatched finite comparison expressions: {a} versus {b}"
  let h ← compute
  let ty ← Lean.Meta.mkHEq a b
  let h ← Lean.Meta.mkAuxTheorem ty h
    (zetaDelta := true) (kind? := `_finiteCongruence)
  cache.modify fun m => m.insert (a, b) h
  return h

-- Explicit comparison congruences are checked within this declaration.
private meta def exactByConversion (h : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let x ← Lean.instantiateMVars (← Lean.Meta.inferType h)
    let y ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let strip (e : Lean.Expr) : Lean.Expr := e.replace fun v =>
      if v.isMData then some v.consumeMData else none
    let x := strip x
    let y := strip y
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let congrCache ← IO.mkRef
      ({} : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem)
    let e ← conversionToEq (← conversionCongruence cache congrCache x y)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[e, h]
    Lean.Elab.Tactic.closeMainGoal `exact result

-- Explicit comparison congruences are checked within this declaration.
private theorem conjugate_cancel
    {C D H : Type*} [Category C] [Category D] [Category H]
    (e : C ≌ D) (F : C ⥤ H) (G : D ⥤ H) (s : e.functor ⋙ G ≅ F) :
    Functor.isoWhiskerLeft e.functor
        ((Functor.leftUnitor G).symm ≪≫
          Functor.isoWhiskerRight e.counitIso.symm G ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse s) ≪≫
      e.funInvIdAssoc F = s := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Equivalence.funInvIdAssoc_hom_app, Category.id_comp, Category.assoc]
  rw [← s.hom.naturality]
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj]
  rw [← G.map_comp_assoc, ← e.counit_app_functor]
  simp only [Iso.inv_hom_id_app]
  change G.map (𝟙 _) ≫ s.hom.app M = _
  simp only [G.map_id, Category.id_comp]

-- Explicit comparison congruences are checked within this declaration.
private theorem change_pull_models
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (S f : D₀ ⥤ D₁) (T g : D₁ ⥤ D₂) (U h : D₀ ⥤ D₂)
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (lF : F ⋙ E₁ ≅ E₀ ⋙ S) (lG : G ⋙ E₂ ≅ E₁ ⋙ T)
    (lH : H ⋙ E₂ ≅ E₀ ⋙ U)
    (eF : f ≅ S) (eG : g ≅ T) (eH : h ≅ U)
    (k : H ≅ F ⋙ G) (kt : U ≅ S ⋙ T) (kc : h ≅ f ⋙ g)
    (hm : eH ≪≫ kt = kc ≪≫ Functor.isoWhiskerLeft f eG ≪≫
      Functor.isoWhiskerRight eF T)
    (M : C₀)
    (hnative : E₂.map (k.hom.app M) ≫ lG.hom.app (F.obj M) ≫
      T.map (lF.hom.app M) = lH.hom.app M ≫ kt.hom.app (E₀.obj M)) :
    E₂.map (k.hom.app M) ≫
      (lG ≪≫ Functor.isoWhiskerLeft E₁ eG.symm).hom.app (F.obj M) ≫
      g.map ((lF ≪≫ Functor.isoWhiskerLeft E₀ eF.symm).hom.app M) =
    (lH ≪≫ Functor.isoWhiskerLeft E₀ eH.symm).hom.app M ≫
      kc.hom.app (E₀.obj M) := by
  apply (cancel_mono
    (eG.hom.app (f.obj (E₀.obj M)) ≫ T.map (eF.hom.app (E₀.obj M)))).mp
  have hn := eG.hom.naturality
    ((lF ≪≫ Functor.isoWhiskerLeft E₀ eF.symm).hom.app M)
  have he := congrArg (fun a ↦ a.hom.app (E₀.obj M)) hm
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app] at he hn ⊢
  dsimp only [Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← T.map_comp, Iso.inv_hom_id_app, Category.comp_id]
  rw [hnative, ← he]
  simp only [Iso.inv_hom_id_app_assoc]

-- Explicit comparison congruences are checked within this declaration.
private theorem model_comp
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    let a := (proEtaleConstantRingPullbackComposition_ordinary h f A).choose
    openSquarePullbackModel A (h ≫ f) ≪≫ sfIntrinsicPullbackComp A h f =
      a ≪≫ Functor.isoWhiskerLeft (proEtaleConstantRingPullback A f)
          (openSquarePullbackModel A h) ≪≫
        Functor.isoWhiskerRight (openSquarePullbackModel A f) (sfIntrinsicPullback A h) := by
  dsimp only
  let a := (proEtaleConstantRingPullbackComposition_ordinary h f A).choose
  have ha := (proEtaleConstantRingPullbackComposition_ordinary h f A).choose_spec.1
  have he (T V : Scheme.{u}) (g : T ⟶ V) :=
    (openSquarePullbackModel_existsUnique A g).exists.choose_spec
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((proEtaleConstantRingAdjunction A (h ≫ f)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change ((sfIntrinsicPullbackComp A h f).hom.app M).val.app _
      (((openSquarePullbackModel A (h ≫ f)).hom.app M).val.app _
        (((proEtaleConstantRingAdjunction A (h ≫ f)).unit.app M).val.app U z)) = _
  erw [he Z X (h ≫ f), finiteIntrinsicPullback_unit_comp]
  let v := (openSquarePullbackModel A h).hom.app
      ((proEtaleConstantRingPullback A f).obj M) ≫
    (sfIntrinsicPullback A h).map ((openSquarePullbackModel A f).hom.app M)
  symm
  change v.val.app _ ((a.hom.app M).val.app _
    (((proEtaleConstantRingAdjunction A (h ≫ f)).unit.app M).val.app U z)) = _
  refine (congrArg (fun t ↦ v.val.app _ t) (ha M U.unop z)).trans ?_
  refine (PresheafOfModules.naturality_apply v.val
    ((MorphismProperty.Over.pullbackComp h f).hom.app U.unop).op _).trans ?_
  congr 1
  change ((sfIntrinsicPullback A h).map ((openSquarePullbackModel A f).hom.app M)).val.app _
    (((openSquarePullbackModel A h).hom.app
      ((proEtaleConstantRingPullback A f).obj M)).val.app _
      (((proEtaleConstantRingAdjunction A h).unit.app
        ((proEtaleConstantRingPullback A f).obj M)).val.app _
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app U z))) = _
  erw [he Z Y h]
  have hn := congrArg (fun k ↦ k.val.app
      (Opposite.op ((proEtaleBaseChange f).obj U.unop))
      (((proEtaleConstantRingAdjunction A f).unit.app M).val.app U z))
    ((sfIntrinsicConstantModuleAdjunction h A).unit.naturality
      ((openSquarePullbackModel A f).hom.app M))
  change ((sfIntrinsicConstantModuleAdjunction h A).unit.app
      ((sfIntrinsicPullback A f).obj M)).val.app _
      (((openSquarePullbackModel A f).hom.app M).val.app _
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app U z)) =
    ((sfIntrinsicPullback A h).map ((openSquarePullbackModel A f).hom.app M)).val.app _
      (((sfIntrinsicConstantModuleAdjunction h A).unit.app
        ((proEtaleConstantRingPullback A f).obj M)).val.app _
          (((proEtaleConstantRingAdjunction A f).unit.app M).val.app U z)) at hn
  erw [← hn, he Y X f]
  rfl
-- Explicit comparison congruences are checked within this declaration.
private def ordinaryComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicModuleEquivalence Y A).functor ⋙ proEtaleConstantRingPullback A f ≅
      upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y A).functor
      (openSquarePullbackModel A f) ≪≫
    (sfIntrinsicModuleEquivalence Y A).funInvIdAssoc _

-- Explicit comparison congruences are checked within this declaration.
private theorem ordinary_comp_square
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    let a := (proEtaleConstantRingPullbackComposition_ordinary h f A).choose
    (sfIntrinsicModuleEquivalence Z A).functor.map
        ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h f).hom.app M) ≫
      (ordinaryComparison A h).inv.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj M) ≫
      (proEtaleConstantRingPullback A h).map ((ordinaryComparison A f).inv.app M) =
    (ordinaryComparison A (h ≫ f)).inv.app M ≫
      a.hom.app ((sfIntrinsicModuleEquivalence X A).functor.obj M) := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let EZ := sfIntrinsicModuleEquivalence Z A
  let F := upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  let G := upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h
  let H := upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (h ≫ f)
  let k := upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h f
  have hn := AlgebraicGeometry.Scheme.transport_comp_square EX EY EZ F G H k M
  have hh := change_pull_models F G H
    (sfIntrinsicPullback A f) (proEtaleConstantRingPullback A f)
    (sfIntrinsicPullback A h) (proEtaleConstantRingPullback A h)
    (sfIntrinsicPullback A (h ≫ f)) (proEtaleConstantRingPullback A (h ≫ f))
    EX.functor EY.functor EZ.functor
    (EX.funInvIdAssoc (F ⋙ EY.functor)).symm
    (EY.funInvIdAssoc (G ⋙ EZ.functor)).symm
    (EX.funInvIdAssoc (H ⋙ EZ.functor)).symm
    (openSquarePullbackModel A f) (openSquarePullbackModel A h)
    (openSquarePullbackModel A (h ≫ f)) k (sfIntrinsicPullbackComp A h f)
    (proEtaleConstantRingPullbackComposition_ordinary h f A).choose
    (model_comp A h f) M hn
  dsimp only [EX, EY, EZ, F, G, H, k, ordinaryComparison,
    Iso.trans, Iso.symm, Functor.isoWhiskerLeft, Functor.whiskerLeft] at hh ⊢
  exact hh

-- Explicit comparison congruences are checked within this declaration.
private theorem exact_comp_square
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    let F := upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
    let G := upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h
    let E := (sfIntrinsicModuleEquivalence Z A).functor.mapDerivedCategory
    E.map ((Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h f) ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso.{u+2,u+2,u+2,u+2,
          u+1,u+2,u+2,u+1,u+1,u+1,u+1,u+1} (ordinaryComparison A h).symm).hom.app
        (F.mapDerivedCategory.obj M) ≫
      (proEtaleConstantRingDerivedPullback A h).map
        ((Functor.mapDerivedCategorySquareIso.{u+2,u+2,u+2,u+2,
          u+1,u+2,u+2,u+1,u+1,u+1,u+1,u+1} (ordinaryComparison A f).symm).hom.app M) =
      (Functor.mapDerivedCategorySquareIso.{u+2,u+2,u+2,u+2,
          u+1,u+2,u+2,u+1,u+1,u+1,u+1,u+1} (ordinaryComparison A (h ≫ f)).symm).hom.app M ≫
        (proEtaleConstantRingPullbackComposition h f A).inv.app
          ((sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory.obj M) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have e := Functor.mapDerivedCategorySquareIso_comp.{u+2,u+2,u+2,u+2,u+2,u+2,
      u+1,u+1,u+1,u+1,u+1,u+1,u+2,u+1,u+1,u+2,u+2,u+1}
    (upperStar B f) (upperStar B h) (upperStar B (h ≫ f))
    (proEtaleConstantRingPullback A f) (proEtaleConstantRingPullback A h)
    (proEtaleConstantRingPullback A (h ≫ f))
    (sfIntrinsicModuleEquivalence X A).functor
    (sfIntrinsicModuleEquivalence Y A).functor
    (sfIntrinsicModuleEquivalence Z A).functor
    (ordinaryComparison A f).symm (ordinaryComparison A h).symm
    (ordinaryComparison A (h ≫ f)).symm (upperStarComp B h f)
    (proEtaleConstantRingPullbackComposition_ordinary h f A).choose
    (ordinary_comp_square A h f)
  rw [(proEtaleConstantRingPullbackComposition_ordinary h f A).choose_spec.2] at e
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc,
    proEtaleConstantRingDerivedPullback] using congrArg (fun t ↦ t.hom.app M) e

-- Explicit comparison congruences are checked within this declaration.
private theorem pasteIsoSquares
    {C : Type*} [Category C] {T U B₁ B₂ I₁ I₂ IT IU : C}
    (k₁ : T ≅ B₁) (k₂ : U ≅ B₂) (t : T ≅ U)
    (q₁ : B₁ ≅ I₁) (q₂ : B₂ ≅ I₂) (pT : T ≅ IT) (pU : U ≅ IU)
    (i₁ : IT ≅ I₁) (i₂ : IU ≅ I₂) (ti : IT ≅ IU)
    (h₁ : k₁.hom ≫ q₁.hom = pT.hom ≫ i₁.hom)
    (h₂ : k₂.hom ≫ q₂.hom = pU.hom ≫ i₂.hom)
    (hc : t.hom ≫ pU.hom = pT.hom ≫ ti.hom) :
    q₁.inv ≫ k₁.inv ≫ t.hom ≫ k₂.hom =
      i₁.inv ≫ ti.hom ≫ i₂.hom ≫ q₂.inv := by
  have h₁' : q₁.hom ≫ i₁.inv = k₁.inv ≫ pT.hom := by
    apply (cancel_epi k₁.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun z ↦ z ≫ i₁.inv) h₁
  apply (cancel_epi q₁.hom).mp
  apply (cancel_mono q₂.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [h₂, ← Category.assoc q₁.hom i₁.inv, h₁']
  simpa only [Category.assoc] using
    congrArg (fun z ↦ k₁.inv ≫ z ≫ i₂.hom) hc

-- Explicit comparison congruences are checked within this declaration.
private def derivedComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor ⋙
        (sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategory ⋙
        proEtaleConstantRingDerivedPullback A f :=
  Functor.isoWhiskerRight
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        f).leftDerivedFunctorIsoMapDerivedCategory
      (sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory ≪≫
    (Functor.mapDerivedCategorySquareIso.{u+2,u+2,u+2,u+2,
      u+2,u+1,u+2,u+1,u+1,u+1,u+1,u+1} (ordinaryComparison A f)).symm

-- Explicit comparison congruences are checked within this declaration.
private theorem native_comp_square
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (M : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicModuleEquivalence Z A).functor.mapDerivedCategory.map
        ((leftDerivedUpperStarComp
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h f).hom.app M) ≫
      (derivedComparison A h).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor.obj M) ≫
      (proEtaleConstantRingDerivedPullback A h).map
        ((derivedComparison A f).hom.app M) =
      (derivedComparison A (h ≫ f)).hom.app M ≫
        (proEtaleConstantRingPullbackComposition h f A).inv.app
          ((sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory.obj M) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have e := exact_comp_square A h f M
  have hs (T V : Scheme.{u}) (a : T ⟶ V) :
      (Functor.mapDerivedCategorySquareIso (ordinaryComparison A a).symm).hom =
        (Functor.mapDerivedCategorySquareIso (ordinaryComparison A a)).inv := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc]
  rw [hs _ _ h, hs _ _ f, hs _ _ (h ≫ f)] at e
  have hn := (Functor.mapDerivedCategorySquareIso
    (ordinaryComparison A h)).inv.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory B f).inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [leftDerivedUpperStarComp_hom_app]
  simp only [derivedComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.symm_hom]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [B, leftDerivedUpperStarIsoMapDerivedCategory] at hn
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only at e
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc] using
    congrArg (fun z ↦ (sfIntrinsicModuleEquivalence Z A).functor.mapDerivedCategory.map
      ((upperStar B (h ≫ f)).leftDerivedFunctorIsoMapDerivedCategory.hom.app M) ≫ z) e

-- Explicit comparison congruences are checked within this declaration.
private theorem native_congr_square
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory.map
        ((leftDerivedUpperStarCongr
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app M) ≫
      (derivedComparison A g).hom.app M =
      (derivedComparison A f).hom.app M ≫
        (eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback A a) h)).hom.app
          ((sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategory.obj M) := by
  subst g
  simp only [leftDerivedUpperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

-- Explicit comparison congruences are checked within this declaration.
private theorem pasteNativeIsoSquares
    {C D J₁ J₂ : Type*} [Category C] [Category D] [Category J₁] [Category J₂]
    (E : C ⥤ D) (P₁ : J₁ ⥤ D) (P₂ : J₂ ⥤ D)
    {T U B₁ B₂ : C} {IT IU : D} {Z₁ Z₁' : J₁} {Z₂ Z₂' : J₂}
    (k₁ : T ≅ B₁) (k₂ : U ≅ B₂) (t : T ≅ U)
    (q₁ : E.obj B₁ ≅ P₁.obj Z₁) (q₁' : Z₁ ≅ Z₁')
    (q₂ : E.obj B₂ ≅ P₂.obj Z₂) (q₂' : Z₂ ≅ Z₂')
    (pT : E.obj T ≅ IT) (pU : E.obj U ≅ IU)
    (i₁ : IT ≅ P₁.obj Z₁') (i₂ : IU ≅ P₂.obj Z₂') (ti : IT ≅ IU)
    (h₁ : E.map k₁.hom ≫ q₁.hom ≫ P₁.map q₁'.hom = pT.hom ≫ i₁.hom)
    (h₂ : E.map k₂.hom ≫ q₂.hom ≫ P₂.map q₂'.hom = pU.hom ≫ i₂.hom)
    (hc : E.map t.hom ≫ pU.hom = pT.hom ≫ ti.hom) :
    P₁.map q₁'.inv ≫ q₁.inv ≫ E.map k₁.inv ≫ E.map t.hom ≫ E.map k₂.hom =
      i₁.inv ≫ ti.hom ≫ i₂.hom ≫ P₂.map q₂'.inv ≫ q₂.inv := by
  have H := pasteIsoSquares (E.mapIso k₁) (E.mapIso k₂) (E.mapIso t)
    (q₁ ≪≫ P₁.mapIso q₁') (q₂ ≪≫ P₂.mapIso q₂') pT pU i₁ i₂ ti
    (by simpa only [Functor.mapIso_hom, Iso.trans_hom, Category.assoc] using h₁)
    (by simpa only [Functor.mapIso_hom, Iso.trans_hom, Category.assoc] using h₂)
    (by simpa only [Functor.mapIso_hom] using hc)
  simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom, Iso.trans_inv,
    Category.assoc] using H

-- Explicit comparison congruences are checked within this declaration.
private theorem pasteFunctorComparisonSquares
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {f : B ⥤ A} {g : D ⥤ B} {h : C ⥤ A} {k : D ⥤ C}
    {fi : B' ⥤ A'} {gi : D' ⥤ B'} {hi : C' ⥤ A'} {ki : D' ⥤ C'}
    (pf : f ⋙ EA ≅ EB ⋙ fi) (pg : g ⋙ EB ≅ ED ⋙ gi)
    (ph : h ⋙ EA ≅ EC ⋙ hi) (pk : k ⋙ EC ≅ ED ⋙ ki)
    {L R : D ⥤ A} {IL IR : D' ⥤ A'}
    (pL : L ⋙ EA ≅ ED ⋙ IL) (pR : R ⋙ EA ≅ ED ⋙ IR)
    (cL : L ≅ g ⋙ f) (cR : R ≅ k ⋙ h) (t : L ≅ R)
    (iL : IL ≅ gi ⋙ fi) (iR : IR ≅ ki ⋙ hi) (ti : IL ≅ IR)
    (M : D)
    (hl : EA.map (cL.hom.app M) ≫ pf.hom.app (g.obj M) ≫
      fi.map (pg.hom.app M) = pL.hom.app M ≫ iL.hom.app (ED.obj M))
    (hr : EA.map (cR.hom.app M) ≫ ph.hom.app (k.obj M) ≫
      hi.map (pk.hom.app M) = pR.hom.app M ≫ iR.hom.app (ED.obj M))
    (hc : EA.map (t.hom.app M) ≫ pR.hom.app M =
      pL.hom.app M ≫ ti.hom.app (ED.obj M)) :
    fi.map (pg.inv.app M) ≫ pf.inv.app (g.obj M) ≫ EA.map (cL.inv.app M) ≫
      EA.map (t.hom.app M) ≫ EA.map (cR.hom.app M) =
    iL.inv.app (ED.obj M) ≫ ti.hom.app (ED.obj M) ≫ iR.hom.app (ED.obj M) ≫
      hi.map (pk.inv.app M) ≫ ph.inv.app (k.obj M) := by
  exact pasteNativeIsoSquares EA fi hi (Iso.app cL M) (Iso.app cR M) (Iso.app t M)
    (Iso.app pf (g.obj M)) (Iso.app pg M)
    (Iso.app ph (k.obj M)) (Iso.app pk M) (Iso.app pL M) (Iso.app pR M)
    (Iso.app iL (ED.obj M)) (Iso.app iR (ED.obj M)) (Iso.app ti (ED.obj M)) hl hr hc

-- Assemble the square over an arbitrary finite ring before specializing its coefficients.
private theorem native_pullback_square (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h f' f g)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (proEtaleConstantRingDerivedPullback A f').map
        ((derivedComparison A g).inv.app M) ≫
      (derivedComparison A f').inv.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          g).leftDerivedFunctor.obj M) ≫
      (sfIntrinsicModuleEquivalence X' A).functor.mapDerivedCategory.map
        ((leftDerivedUpperStarSquareIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).hom.app M) =
    (proEtaleConstantRingPullbackComposition f' g A ≪≫
        eqToIso (congrArg (fun a ↦
          proEtaleConstantRingDerivedPullback A a) sq.w.symm) ≪≫
        (proEtaleConstantRingPullbackComposition h f A).symm).hom.app
          ((sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategory.obj M) ≫
      (proEtaleConstantRingDerivedPullback A h).map
        ((derivedComparison A f).inv.app M) ≫
      (derivedComparison A h).inv.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          f).leftDerivedFunctor.obj M) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have he := pasteFunctorComparisonSquares
    (derivedComparison A f') (derivedComparison A g)
    (derivedComparison A h) (derivedComparison A f)
    (derivedComparison A (f' ≫ g)) (derivedComparison A (h ≫ f))
    (leftDerivedUpperStarComp B f' g) (leftDerivedUpperStarComp B h f)
    (leftDerivedUpperStarCongr B sq.w.symm)
    (proEtaleConstantRingPullbackComposition f' g A).symm
    (proEtaleConstantRingPullbackComposition h f A).symm
    (eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback A a) sq.w.symm)) M
    (by
      have H := native_comp_square A f' g M
      simp only [Iso.symm_hom]
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
        exactByConversion h)
    (by
      have H := native_comp_square A h f M
      simp only [Iso.symm_hom]
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
        exactByConversion h)
    (by
      have H := native_congr_square A sq.w.symm M
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
        exactByConversion h)
  simp only [B, Iso.symm_hom, Iso.symm_inv, leftDerivedUpperStarSquareIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at he ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `he) none
    exactByConversion h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option linter.style.haveILetI false in
-- Inlining the finite instance keeps the concrete realization conversions small.
-- Explicit comparison congruences are checked within this declaration.
/-- The fixed scalar pullback comparisons identify the two pullback-square words.
Source: blueprint operations proof (2), pullback compositor normalization.
(blueprint: new-lem-sp-strict-finite-pullback-square-coherence).

Proof: compare the ordinary pullback compositors by transposing under the
constant-ring pullback adjunction. The normalization of openSquarePullbackModel
and the unit-composition formula for sfIntrinsicPullbackComp identify both
transposes sectionwise. Combine this with the equivalence triangle identities
to obtain the compositor square for comparisonFiniteOrdinaryPull. Localize
that equation with mapDerivedCategorySquareIso_comp and the published ordinary
normalization of proEtaleConstantRingPullbackComposition. Insert the native
left-derived/exact comparison, using its definition for both compositors.
Apply the resulting equation to f′,g and to h,f. Transport along sq.w and cancel
the comparisons for the common composite. Inverting the boundary comparisons
yields the displayed square. This is independent of direct-image adjunctions,
properness, compactification and witnesses. -/
theorem strictFinitePullbackSquareCoherence (b : Base l E)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h f' f g) (n : ℕ)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (proEtaleConstantRingDerivedPullback (R l E n) f').map
        ((comparisonFinitePull l E b g n).inv.app M) ≫
      (comparisonFinitePull l E b f' n).inv.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          g).leftDerivedFunctor.obj M) ≫
      (comparisonFiniteRealization l E b X' n).map
        ((leftDerivedUpperStarSquareIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq.toCommSq).hom.app M) =
    (proEtaleConstantRingPullbackComposition f' g (R l E n) ≪≫
        eqToIso (congrArg (fun a ↦
          proEtaleConstantRingDerivedPullback (R l E n) a) sq.w.symm) ≪≫
        (proEtaleConstantRingPullbackComposition h f (R l E n)).symm).hom.app
          ((comparisonFiniteRealization l E b Y n).obj M) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) h).map
        ((comparisonFinitePull l E b f n).inv.app M) ≫
      (comparisonFinitePull l E b h n).inv.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          f).leftDerivedFunctor.obj M) := by
  letI := b.finite n
  have H := native_pullback_square (R l E n) sq M
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
    exactByConversion h

end AlgebraicGeometry.ProEtale.SpTowerShriek
