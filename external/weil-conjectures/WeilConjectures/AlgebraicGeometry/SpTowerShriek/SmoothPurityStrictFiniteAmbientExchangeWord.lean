/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteProperExchangeFace
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteOpenExchangeFace

/-! Finite exchange comparisons in fixed scalar coordinates. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 30000] SheafOfModules.instAbelian
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
set_option maxRecDepth 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftAdjoint AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  CategoryTheory.Limits.limit.cone CategoryTheory.Limits.colimit.cocone
  CategoryTheory.sheafificationAdjunction CategoryTheory.presheafToSheaf
  CategoryTheory.eqToIso CategoryTheory.eqToHom
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

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
          ``CategoryTheory.Functor.comp, ``Compactification.ofIsPullback,
          ``CategoryTheory.Functor.isoWhiskerLeft, ``CategoryTheory.Functor.isoWhiskerRight,
          ``comparisonFiniteF, ``comparisonLevelExchange, ``finiteF,
          ``rightDerivedLowerShriekOfCompactification]
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
private theorem replaceExchangeArrow
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {Z : D} {a a' : X ⟶ Y}
    {b : F.obj Y ⟶ Z} {c : F.obj X ⟶ Z}
    (ha : a = a') (hc : F.map a' ≫ b = c) : F.map a ≫ b = c := by
  rw [ha]
  exact hc

section Pasting
variable {X Z Y X' Z' Y' IX IZ IY IX' IZ' IY' : Type*}
  [Category X] [Category Z] [Category Y] [Category X'] [Category Z'] [Category Y']
  [Category IX] [Category IZ] [Category IY] [Category IX'] [Category IZ'] [Category IY']

-- Explicit comparison congruences are checked within this declaration.
private theorem pasteExchangeWords
    (J : X ⥤ Z) (R : Z ⥤ Y) (G : Y ⥤ Y') (P : Z ⥤ Z') (H : X ⥤ X')
    (J' : X' ⥤ Z') (R' : Z' ⥤ Y')
    (j : IX ⥤ IZ) (r : IZ ⥤ IY) (g : IY ⥤ IY') (p : IZ ⥤ IZ') (h : IX ⥤ IX')
    (j' : IX' ⥤ IZ') (r' : IZ' ⥤ IY')
    (ex : X ⥤ IX) (ez : Z ⥤ IZ) (ey : Y ⥤ IY)
    (ex' : X' ⥤ IX') (ez' : Z' ⥤ IZ') (ey' : Y' ⥤ IY')
    (a : R ⋙ G ⟶ P ⋙ R')
    (P₀ : Z ⥤ Z') (H₀ : X ⥤ X') (sP : P ≅ P₀) (sH : H ≅ H₀)
    (b₀ : H₀ ⋙ J' ≅ J ⋙ P₀)
    (ai : r ⋙ g ⟶ p ⋙ r') (bi : j ⋙ p ⟶ h ⋙ j')
    (cj : J ⋙ ez ≅ ex ⋙ j) (cr : R ⋙ ey ≅ ez ⋙ r)
    (cg : G ⋙ ey' ≅ ey ⋙ g) (cp : P ⋙ ez' ≅ ez ⋙ p)
    (ch : H ⋙ ex' ≅ ex ⋙ h) (cj' : J' ⋙ ez' ≅ ex' ⋙ j')
    (cr' : R' ⋙ ey' ≅ ez' ⋙ r')
    (N : X)
    (ha : ey'.map (a.app (J.obj N)) ≫ cr'.hom.app (P.obj (J.obj N)) ≫
        r'.map (cp.hom.app (J.obj N)) =
      cg.hom.app (R.obj (J.obj N)) ≫ g.map (cr.hom.app (J.obj N)) ≫
        ai.app (ez.obj (J.obj N)))
    (hb : ez'.map
        ((Functor.isoWhiskerRight sH J' ≪≫ b₀ ≪≫
          Functor.isoWhiskerLeft J sP.symm).inv.app N) ≫
        cj'.hom.app (H.obj N) ≫ j'.map (ch.hom.app N) =
      cp.hom.app (J.obj N) ≫ p.map (cj.hom.app N) ≫ bi.app (ex.obj N)) :
    ey'.map (((Functor.associator J R G).hom ≫ Functor.whiskerLeft J a ≫
        ((Functor.associator J P R').symm ≪≫
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft J sP ≪≫ b₀.symm ≪≫
              Functor.isoWhiskerRight sH.symm J') R' ≪≫
            Functor.associator H J' R')).hom).app N) ≫
      (Functor.isoWhiskerLeft J' cr' ≪≫ Functor.isoWhiskerRight cj' r').hom.app
        (H.obj N) ≫
      (j' ⋙ r').map (ch.hom.app N) =
    cg.hom.app ((J ⋙ R).obj N) ≫
      g.map ((Functor.isoWhiskerLeft J cr ≪≫ Functor.isoWhiskerRight cj r).hom.app N) ≫
      ((Functor.associator j r g).hom ≫ Functor.whiskerLeft j ai ≫
        (Functor.associator j p r').inv ≫ Functor.whiskerRight bi r' ≫
        (Functor.associator h j' r').hom).app (ex.obj N) := by
  have hr := cr'.hom.naturality
    ((Functor.isoWhiskerRight sH J' ≪≫ b₀ ≪≫
      Functor.isoWhiskerLeft J sP.symm).inv.app N)
  have hi := ai.naturality (cj.hom.app N)
  dsimp only [Functor.comp_map] at hr hi
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc] at hr hb ⊢
  rw [reassoc_of% hr]
  simp only [← r'.map_comp]
  rw [hb]
  simp only [r'.map_comp]
  rw [reassoc_of% ha]
  rw [← reassoc_of% hi]

end Pasting

-- Explicit comparison congruences are checked within this declaration.
private abbrev nativeD (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
-- Explicit comparison congruences are checked within this declaration.
private abbrev nativeOpen (A : Type u) [CommRing A]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory
-- Explicit comparison congruences are checked within this declaration.
private abbrev nativePush (A : Type u) [CommRing A]
    {U V : Scheme.{u}} (f : U ⟶ V) :=
  (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor
-- Explicit comparison congruences are checked within this declaration.
private abbrev nativePull (A : Type u) [CommRing A]
    {U V : Scheme.{u}} (f : U ⟶ V) :=
  (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor

section NativePasting
variable {IX IZ IY IX' IZ' IY' : Type*}
  [Category IX] [Category IZ] [Category IY] [Category IX'] [Category IZ'] [Category IY']

-- Explicit comparison congruences are checked within this declaration.
private theorem pasteNativeExchangeWords (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f)
    (j : IX ⥤ IZ) (r : IZ ⥤ IY) (γ : IY ⥤ IY') (p : IZ ⥤ IZ') (η : IX ⥤ IX')
    (j' : IX' ⥤ IZ') (r' : IZ' ⥤ IY')
    (ex : nativeD A X ⥤ IX) (ez : nativeD A c.Z ⥤ IZ) (ey : nativeD A Y ⥤ IY)
    (ex' : nativeD A X' ⥤ IX') (ez' : nativeD A (c.ofIsPullback sq).Z ⥤ IZ') (ey' : nativeD A Y'
      ⥤ IY')
    (L : IY ⥤ IZ) (L' : IY' ⥤ IZ') (adj : L ⊣ r) (adj' : L' ⊣ r')
    (theta : γ ⋙ L' ≅ L ⋙ p) (beta : j ⋙ p ≅ η ⋙ j')
    (cj : (nativeOpen A c.i) ⋙ ez ≅ ex ⋙ j) (cr : (nativePush A c.g) ⋙ ey ≅ ez ⋙ r)
    (cg : (nativePull A g) ⋙ ey' ≅ ey ⋙ γ) (cp : (nativePull A (pullback.fst c.g g)) ⋙ ez' ≅ ez ⋙ p)
    (ch : (nativePull A h) ⋙ ex' ≅ ex ⋙ η) (cj' : (nativeOpen A (c.ofIsPullback sq).i) ⋙ ez' ≅
      ex' ⋙ j')
    (cr' : (nativePush A (c.ofIsPullback sq).g) ⋙ ey' ≅ ez' ⋙ r')
    (N : nativeD A X)
    (ha : ey'.map (((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app ((nativeOpen A c.i).obj N))) ≫
      cr'.hom.app ((nativePull A (pullback.fst c.g g)).obj ((nativeOpen A c.i).obj N)) ≫
        r'.map (cp.hom.app ((nativeOpen A c.i).obj N)) =
      cg.hom.app ((nativePush A c.g).obj ((nativeOpen A c.i).obj N)) ≫ γ.map (cr.hom.app
      ((nativeOpen A c.i).obj N)) ≫
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ theta.hom)).app
          (ez.obj ((nativeOpen A c.i).obj N)))
    (hb : ez'.map
        ((leftDerivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (c.isPullback_i_ofIsPullback sq)).inv.app N) ≫
        cj'.hom.app ((nativePull A h).obj N) ≫ j'.map (ch.hom.app N) =
      cp.hom.app ((nativeOpen A c.i).obj N) ≫ p.map (cj.hom.app N) ≫ beta.hom.app (ex.obj N)) :
    ey'.map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq c).app N) ≫
      (Functor.isoWhiskerLeft (nativeOpen A (c.ofIsPullback sq).i) cr' ≪≫ Functor.isoWhiskerRight
      cj' r').hom.app
        ((nativePull A h).obj N) ≫
      (j' ⋙ r').map (ch.hom.app N) =
    cg.hom.app (((nativeOpen A c.i) ⋙ (nativePush A c.g)).obj N) ≫
      γ.map ((Functor.isoWhiskerLeft (nativeOpen A c.i) cr ≪≫ Functor.isoWhiskerRight cj
      r).hom.app N) ≫
      (CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
        j j' L r adj L' r' adj' γ η p theta beta).app (ex.obj N)  := by
  exact pasteExchangeWords
    (nativeOpen A c.i) (nativePush A c.g) (nativePull A g)
    (nativePull A (pullback.fst c.g g)) (nativePull A h)
    (nativeOpen A (c.ofIsPullback sq).i) (nativePush A (c.ofIsPullback sq).g)
    j r γ p η j' r' ex ez ey ex' ez' ey'
    (derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (c.isPullback_g_ofIsPullback
      sq).flip.toCommSq)
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst c.g g)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst c.g g))
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h)
    (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (c.isPullback_i_ofIsPullback sq))
    (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ theta.hom)) beta.hom
    cj cr cg cp ch cj' cr' N ha hb

end NativePasting

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The ambient faces share their categorical parameters. Keep these parameters
-- fixed in congruence rules, and share the resulting proof expressions. Only
-- definitional reductions and reusable congruence rules need certificates.
private meta partial def finiteAmbientCongruence
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (congrCache : IO.Ref (Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem))
    (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← Lean.Meta.mkHEqRefl a
  if let some h := (← cache.get).get? (a, b) then return h
  let h ← do
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    else if (← Lean.Meta.isClass? (← Lean.Meta.inferType a)).isSome then
      conversionReduction a b
    else if a.getAppFn == b.getAppFn && a.isApp &&
        a.getAppNumArgs == b.getAppNumArgs then do
      let allA := a.getAppArgs
      let allB := b.getAppArgs
      let mut common := 0
      while common < allA.size && allA[common]! == allB[common]! do
        common := common + 1
      let head := Lean.mkAppN a.getAppFn (allA.extract 0 common)
      let aa := allA.extract common allA.size
      let bb := allB.extract common allB.size
      let key := (head, aa.size)
      let ct ← match (← congrCache.get).get? key with
        | some ct => pure ct
        | none => do
          let ct ← Lean.Meta.mkHCongrWithArity head aa.size
          let proof ← Lean.Meta.mkAuxTheorem ct.type ct.proof
            (kind? := `_finiteAmbientCongruence)
          let ct := { ct with proof := proof }
          congrCache.modify fun m => m.insert key ct
          pure ct
      let mut args := #[]
      for i in [:aa.size] do
        let h ← finiteAmbientCongruence cache congrCache aa[i]! bb[i]!
        let h ← if ct.argKinds[i]! == .eq then conversionToEq h else pure h
        args := args ++ #[aa[i]!, bb[i]!, h]
      let h := Lean.mkAppN ct.proof args
      if (← Lean.Meta.inferType h).isHEq then pure h else conversionOfEq h
    else
      conversionCongruence cache congrCache a b
  cache.modify fun m => m.insert (a, b) h
  return h

private meta def exactFiniteAmbient (h : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let strip (e : Lean.Expr) : Lean.Expr := e.replace fun v =>
    if v.isMData then some v.consumeMData else none
  let x := strip (← Lean.instantiateMVars (← Lean.Meta.inferType h))
  let y := strip (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget))
  let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
  let congrCache ← IO.mkRef
    ({} : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem)
  let e ← conversionToEq (← finiteAmbientCongruence cache congrCache x y)
  let result ← Lean.Meta.mkAppM ``Eq.mp #[e, h]
  Lean.Elab.Tactic.closeMainGoal `exact result

-- Explicit comparison congruences are checked within this declaration.
/-- Ambient scalar comparison after replacing the retained etale witness by the
canonical pro-etale compactification base-change map.
Source: blueprint operations proof (2), finite exchange word.
The proper mate and the open exchange are transported independently through the
fixed scalar pullback square, and their pasted word is the displayed equation.
-/
private theorem strictFiniteAmbientExchangeCore (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    (coordinates : StrictFiniteCoordinates l E b) :
    ∀ {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f]
      (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ)
      (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))),
      (comparisonFiniteRealization l E b Y' n).map
          ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq c).app N) ≫
        (comparisonFiniteF l E b coordinates (c.ofIsPullback sq) n).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            h).leftDerivedFunctor.obj N) ≫
        (finiteF l E b (c.ofIsPullback sq) n).map
          ((comparisonFinitePull l E b h n).hom.app N) =
      (comparisonFinitePull l E b g n).hom.app
          ((rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).obj N) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) g).map
          ((comparisonFiniteF l E b coordinates c n).hom.app N) ≫
        (comparisonLevelExchange l E b o levels sq c n).app
          ((comparisonFiniteRealization l E b X n).obj N) := by
  intro X' X Y' Y h f' f g _ _ _ sq c n N
  have hp := strictFiniteProperExchangeFace l E b coordinates
    (c.isPullback_g_ofIsPullback sq).flip n
    ((openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i).mapDerivedCategory.obj N)
  have ho := strictFiniteOpenExchangeFace l E b o levels
    (c.isPullback_i_ofIsPullback sq) n N
  have H := pasteNativeExchangeWords (R l E n) sq c
    (sfIntrinsicDerivedOpen (R l E n) c.i)
    (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor
    (proEtaleConstantRingDerivedPullback (R l E n) g)
    (proEtaleConstantRingDerivedPullback (R l E n) (pullback.fst c.g g))
    (proEtaleConstantRingDerivedPullback (R l E n) h)
    (sfIntrinsicDerivedOpen (R l E n) (c.ofIsPullback sq).i)
    (proEtaleConstantRingPushforward (R l E n) (c.ofIsPullback sq).g).rightDerivedFunctor
    (comparisonFiniteRealization l E b X n) (comparisonFiniteRealization l E b c.Z n)
    (comparisonFiniteRealization l E b Y n) (comparisonFiniteRealization l E b X' n)
    (comparisonFiniteRealization l E b (c.ofIsPullback sq).Z n)
    (comparisonFiniteRealization l E b Y' n)
    (proEtaleConstantRingDerivedPullback (R l E n) c.g)
    (proEtaleConstantRingDerivedPullback (R l E n) (c.ofIsPullback sq).g)
    (proEtaleConstantRingAdjunction (R l E n) c.g).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleConstantRingAdjunction (R l E n)
      (c.ofIsPullback sq).g).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleConstantRingPullbackComposition (c.ofIsPullback sq).g g (R l E n) ≪≫
      eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
        pullback.condition.symm) ≪≫
      (proEtaleConstantRingPullbackComposition (pullback.fst c.g g) c.g (R l E n)).symm)
    (levels.openExchange h (c.ofIsPullback sq).i c.i (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback sq) n)
    (comparisonFiniteOpen l E b c.i n) (coordinates.val c.g n).right
    (comparisonFinitePull l E b g n) (comparisonFinitePull l E b (pullback.fst c.g g) n)
    (comparisonFinitePull l E b h n) (comparisonFiniteOpen l E b (c.ofIsPullback sq).i n)
    (coordinates.val (c.ofIsPullback sq).g n).right N
    (by
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hp) none
        exactFiniteAmbient h)
    (by
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `ho) none
        exactFiniteAmbient h)
  -- Normalize the visible word before comparing its remaining instance diamonds.
  simp only [comparisonFiniteF, comparisonLevelExchange, finiteF,
    nativeOpen, nativePush, nativePull, rightDerivedLowerShriekOfCompactification,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc] at H ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
    exactFiniteAmbient h

-- Explicit comparison congruences are checked within this declaration.
/-- The retained witness transport equals the ambient
compactification base-change map.
Source: blueprint operations proof (2), individual etale-origin transport.
The second conjunct of `compactSupport_exchange_transport` identifies the
witness transport at each specified witness.
-/
private theorem strictFiniteWitnessTransport (b : Base l E)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (alpha : (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) X).mapDerivedCategory.obj L.obj ≅ N) :
    compactExchangeTransportAtWitness (ULift.{u + 1, u} (R l E n))
      sq c L N alpha =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq c).app N := by
  exact (compactSupport_exchange_transport
    (ULift.{u + 1, u} (R l E n)) sq c).2 L N alpha

end AlgebraicGeometry.ProEtale.SpTowerShriek
