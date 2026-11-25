/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFinitePullbackSquareCoherence
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube

/-! # Fixed-scalar compatibility of one exchange face -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 30000] SheafOfModules.instAbelian
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftAdjoint AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  CategoryTheory.Limits.limit.cone CategoryTheory.Limits.colimit.cocone
  CategoryTheory.sheafificationAdjunction CategoryTheory.presheafToSheaf
  CategoryTheory.eqToIso CategoryTheory.eqToHom
attribute [local irreducible] CategoryTheory.mateEquiv
  CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction
  AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction
attribute [local irreducible] _root_.instCategoryDerivedCategory
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
private theorem coordinates_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {e : C ⥤ C'} {d : D ⥤ D'} {L : C ⥤ D} {G : D ⥤ C}
    {l : C' ⥤ D'} {g : D' ⥤ C'} {adj : L ⊣ G} {level : l ⊣ g}
    (coordinates : ComparisonAdjunctionCoordinates e d adj level)
    (p : L ⋙ d ≅ e ⋙ l) (hp : coordinates.left = p) :
    (mateEquiv adj level (TwoSquare.mk _ _ _ _ p.inv)) =
      coordinates.right.hom := by
  subst p
  ext N
  apply (level.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  exact (coordinates.counit N).symm

-- Explicit comparison congruences are checked within this declaration.
private theorem coordinates_cube_maps
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (e : R ⋙ G ⟶ H ⋙ S) (e' : R' ⋙ G' ⟶ H' ⋙ S')
    (he : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)) = e)
    (he' : (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')) = e')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (coordinatesF : ComparisonAdjunctionCoordinates a b adj adj')
    (coordinatesK : ComparisonAdjunctionCoordinates c d adjK adjK')
    (hF : coordinatesF.left = pF) (hK : coordinatesK.left = pK) :
    c.map (e.app E) ≫
        coordinatesK.right.hom.app (H.obj E) ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫ G'.map (coordinatesF.right.hom.app E) ≫
        e'.app (b.obj E) := by
  exact exchangeMate_cube_all_normalized adj adjK adj' adjK' a b c d pF pG pH pK
    θ θ' hc E (coordinatesF.right.hom.app E)
    (coordinatesK.right.hom.app (H.obj E)) (e.app E) (e'.app (b.obj E))
    (NatTrans.congr_app he E) (NatTrans.congr_app he' (b.obj E))
    (NatTrans.congr_app (coordinates_mate coordinatesF pF hF) E)
    (NatTrans.congr_app (coordinates_mate coordinatesK pK hK) (H.obj E))

-- Explicit comparison congruences are checked within this declaration.
private theorem coordinates_cube_from_coordinates
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    {adj : F ⊣ R} {adjK : K ⊣ S} {adj' : F' ⊣ R'} {adjK' : K' ⊣ S'}
    {a : A ⥤ A'} {b : B ⥤ B'} {c : C ⥤ C'} {d : D ⥤ D'}
    (coordinatesF : ComparisonAdjunctionCoordinates a b adj adj')
    (coordinatesK : ComparisonAdjunctionCoordinates c d adjK adjK')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (e : R ⋙ G ⟶ H ⋙ S)
    (he : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)) = e)
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (hF : coordinatesF.left = pF) (hK : coordinatesK.left = pK) :
    c.map (e.app E) ≫
        coordinatesK.right.hom.app (H.obj E) ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫ G'.map (coordinatesF.right.hom.app E) ≫
        (mateEquiv adj' adjK' (TwoSquare.mk G' F' K' H' θ')).app (b.obj E) := by
  exact coordinates_cube_maps adj adjK adj' adjK' a b c d pF pG pH pK θ θ'
    e (mateEquiv adj' adjK' (TwoSquare.mk G' F' K' H' θ')) he rfl hc E
    coordinatesF coordinatesK hF hK

-- Explicit comparison congruences are checked within this declaration.
private theorem native_base_change_mate (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq h f' f g) :
    (mateEquiv
      (derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      (derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f')
      (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq).hom)) =
      derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq := by
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Explicit comparison congruences are checked within this declaration.
/-- Fixed-scalar realization preserves the proper base-change mate.
Source: blueprint operations proof (2), finite proper exchange face.
(blueprint: new-lem-sp-strict-finite-proper-exchange-face).

Proof: strictFinitePullbackSquareCoherence identifies the inverse-image cube
for the four fixed scalar comparisons. The coordinates' counit equations
identify the two vertical mates with their right comparisons, by injectivity
of adjunction transposition. Apply exchangeMate_cube and substitute these
two mate identifications. Its component equation is exactly the displayed
proper exchange face; derivedBaseChangeMap is the native mate by definition.
This works for every unbounded object, including zero objects, and does not
assert that either exchange is invertible. -/
theorem strictFiniteProperExchangeFace (b : Base l E)
    (coordinates : StrictFiniteCoordinates l E b)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h f' f g) (n : ℕ)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b Y' n).map
        ((derivedBaseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq.toCommSq).app N) ≫
      (coordinates.val f' n).right.hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          h).leftDerivedFunctor.obj N) ≫
      (proEtaleConstantRingPushforward (R l E n) f').rightDerivedFunctor.map
        ((comparisonFinitePull l E b h n).hom.app N) =
    (comparisonFinitePull l E b g n).hom.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          f).rightDerivedFunctor.obj N) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) g).map
        ((coordinates.val f n).right.hom.app N) ≫
      (mateEquiv
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (proEtaleConstantRingAdjunction (R l E n) f))
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (proEtaleConstantRingAdjunction (R l E n) f'))
        (TwoSquare.mk
          (proEtaleConstantRingDerivedPullback (R l E n) g)
          (proEtaleConstantRingDerivedPullback (R l E n) f)
          (proEtaleConstantRingDerivedPullback (R l E n) f')
          (proEtaleConstantRingDerivedPullback (R l E n) h)
          (proEtaleConstantRingPullbackComposition f' g (R l E n) ≪≫
            eqToIso (congrArg (fun a ↦
              proEtaleConstantRingDerivedPullback (R l E n) a) sq.w.symm) ≪≫
            (proEtaleConstantRingPullbackComposition h f (R l E n)).symm).hom)
        ).app ((comparisonFiniteRealization l E b X n).obj N)   := by
  have H := coordinates_cube_from_coordinates
    (coordinates.val f n) (coordinates.val f' n)
    (comparisonFinitePull l E b f n) (comparisonFinitePull l E b g n)
    (comparisonFinitePull l E b h n) (comparisonFinitePull l E b f' n)
    (leftDerivedUpperStarSquareIso
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq.toCommSq).hom
    (proEtaleConstantRingPullbackComposition f' g (R l E n) ≪≫
      eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
        sq.w.symm) ≪≫
      (proEtaleConstantRingPullbackComposition h f (R l E n)).symm).hom
    (derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq.toCommSq)
    (by rfl)
    (by
      intro M
      have HC := strictFinitePullbackSquareCoherence l E b sq n M
      -- Normalize structural projections before constructing instance congruences.
      dsimp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app] at HC ⊢
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `HC) none
        exactByConversion h)
    N (coordinates.property f n) (coordinates.property f' n)
  dsimp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app] at H ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
    exactByConversion h

end AlgebraicGeometry.ProEtale.SpTowerShriek
