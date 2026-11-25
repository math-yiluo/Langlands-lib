/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import all WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteCoordinateCalculus
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.OpenScalarExchangeMate
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFinitePullbackSquareCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
/-! # Fixed-scalar realization of the open exchange face -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 30000] SheafOfModules.instAbelian
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstructibleExceptionalCoefficients
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
    if a.isAppOf ``CategoryTheory.Functor.obj then
      let a' ← Lean.Meta.withTransparency .all (Lean.Meta.whnf a)
      let a' ← match (← reduce a') with
        | some v => pure v
        | none => pure a'
      if a' != a then
        return ← conversionTrans (← conversionReduction a a')
          (← conversionCongruence cache congrCache a' b)
    if b.isAppOf ``CategoryTheory.Functor.obj then
      let b' ← Lean.Meta.withTransparency .all (Lean.Meta.whnf b)
      let b' ← match (← reduce b') with
        | some v => pure v
        | none => pure b'
      if b' != b then
        return ← conversionTrans (← conversionCongruence cache congrCache a b')
          (← conversionSymm (← conversionReduction b b'))
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
private theorem conjugate_open_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ C') (f : D ≌ D') {J : C ⥤ D} {U : D ⥤ C}
    (adj : J ⊣ U) {P : D' ⥤ C'} (q : P ≅ f.inverse ⋙ U ⋙ e.functor) (K : C) :
    (((e.symm.toAdjunction.comp adj).comp f.toAdjunction).ofNatIsoRight q.symm).unit.app
        (e.functor.obj K) ≫
      P.map (f.functor.map (J.map (e.unitIso.inv.app K))) =
    e.functor.map (adj.unit.app K) ≫
      (f.funInvIdAssoc (U ⋙ e.functor)).inv.app (J.obj K) ≫
      q.inv.app (f.functor.obj (J.obj K)) := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  rw [← q.inv.naturality]
  rw [← Category.assoc, transported_open_unit]
  simp only [Equivalence.funInvIdAssoc_inv_app, Equivalence.unit, Category.assoc,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj]

-- Explicit comparison congruences are checked within this declaration.
private theorem ordinary_open_unit
    (A : Type u) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (N : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    let e := sfIntrinsicModuleEquivalence U A
    let f := sfIntrinsicModuleEquivalence T A
    let J := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
    let a := (sfIntrinsicOpenAdjunction A j).ofNatIsoRight
      (openSquarePullbackModel A j).symm
    let v := Functor.isoWhiskerLeft f.functor (openSquarePullbackModel A j) ≪≫
      f.funInvIdAssoc (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙ e.functor)
    a.unit.app (e.functor.obj N) ≫
      (proEtaleConstantRingPullback A j).map ((e.funInvIdAssoc (J ⋙ f.functor)).hom.app N) =
    e.functor.map ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app N) ≫
      v.inv.app (J.obj N) := by
  dsimp only
  simpa only [sfIntrinsicOpenAdjunction, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Equivalence.funInvIdAssoc_hom_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
    Equivalence.unitInv, Category.assoc] using
    conjugate_open_unit (sfIntrinsicModuleEquivalence U A)
      (sfIntrinsicModuleEquivalence T A)
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
      (openSquarePullbackModel A j) N

-- Exact adjunction normalization, proved directly from localization unit formulas.
-- Localization comparison is checked within this declaration.
private theorem quotient_hom_id {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).hom.app J = 𝟙 _ := rfl

-- Localization comparison is checked within this declaration.
private theorem quotient_inv_id {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).inv.app J = 𝟙 _ := rfl

-- Localization comparison is checked within this declaration.
private theorem homotopyFactors_inv_id {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] (F : B ⥤ E) [F.Additive] (J : CochainComplex B ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J = 𝟙 _ := rfl

-- Localization comparison is checked within this declaration.
private theorem factorsh_hom {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj J) =
      F.mapDerivedCategoryFactors.hom.app J := by
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app, quotient_hom_id, quotient_inv_id,
    homotopyFactors_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id]

-- Localization comparison is checked within this declaration.
private theorem map_iso_word
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} (e : X ≅ Y) {Z W : B} (d : F.obj Y ≅ Z) (u : W ⟶ Z) :
    u ≫ d.inv ≫ F.map e.inv ≫ F.map e.hom ≫ d.hom = u := by
  rw [← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp,
    d.inv_hom_id, Category.comp_id]

-- Localization comparison is checked within this declaration.
private theorem exact_adjunction_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [aL : L.Additive] [aR : R.Additive]
    [lL : PreservesFiniteLimits L] [cL : PreservesFiniteColimits L]
    [lR : PreservesFiniteLimits R] [cR : PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = exactLocalizationDerivedAdjunction a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  let K' := (HomotopyCategory.quotient A (.up ℤ)).obj K
  have hs : (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    change (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Qh.obj K') ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') = _
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc]
    erw [← R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K'
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Qh.obj K') ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K') = _ at hu
    erw [reassoc_of% hu]
    have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((L.mapHomotopyCategory (.up ℤ)).obj K')
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [← Category.assoc (R.rightDerivedFunctorUnit.app _), hf,
      Iso.inv_hom_id_app, Category.comp_id]
  have he : (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    have hl := factorsh_hom L K
    have hr := factorsh_hom R
      ((L.mapHomologicalComplex (.up ℤ)).obj K)
    change L.mapDerivedCategoryFactorsh.hom.app K' = _ at hl
    change R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj K') = _ at hr
    have hmap : DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
      dsimp only [K']
      rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
      rfl
    erw [hl, hr, ← hmap, CategoryTheory.exact_unit_app]
    convert map_iso_word R.mapDerivedCategory (L.mapDerivedCategoryFactors.app K)
      (R.mapDerivedCategoryFactors.app ((L.mapHomologicalComplex (.up ℤ)).obj K))
      (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K)) using 1 <;>
      first | rfl | simp only [Iso.app_hom, Iso.app_inv, Category.assoc]
  exact (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K'))).mp
    (by
      have hh := hs.trans he.symm
      simp only [Functor.comp_obj] at hh
      convert hh using 1)

-- Localization comparison is checked within this declaration.
private theorem fixed_open_exact_adjunction
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) j =
      exactLocalizationDerivedAdjunction
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j) := by
  let a := ProEtale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  let L := ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  have he : a.mapDerivedCategoryRightDerivedAdjunction =
      a.derivedAdjunction.ofNatIsoLeft L.leftDerivedFunctorIsoMapDerivedCategory := by
    refine (a.mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      L.leftDerivedFunctorIsoMapDerivedCategory.symm ?_
    ext H
    simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [← L.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
    rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]
  rw [← exact_adjunction_eq a,
    he]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option linter.style.haveILetI false in
-- Inline the local instances to keep the derived comparison expressions small.
-- Explicit comparison congruences are checked within this declaration.
private theorem strict_finite_open_unit (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (N : DerivedCategory (Sheaf (ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonLevelOpenAdjunction l E b j n).unit.app
        ((comparisonFiniteRealization l E b U n).obj N) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) j).map
        ((comparisonFiniteOpen l E b j n).inv.app N) =
    (comparisonFiniteRealization l E b U n).map
        ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).unit.app N) ≫
      (comparisonFinitePull l E b j n).hom.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).mapDerivedCategory.obj N) := by
  letI := b.finite n
  letI := sfIntrinsicExtensionByZero_additive j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteLimits j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteColimits j (R l E n)
  have ht := exact_unit_square
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j)
    (finiteOpenAdjunction l E b j n)
    (comparisonFiniteOrdinaryPull l E b j n).symm
    (comparisonFiniteOrdinaryOpen l E b j n).symm
    (fun K ↦ by
      simpa only [finiteOpenAdjunction, comparisonFiniteOrdinaryPull,
        comparisonFiniteOrdinaryOpen, Iso.symm_hom, Iso.symm_inv] using
        ordinary_open_unit (R l E n) j K) N
  rw [← fixed_open_exact_adjunction (R l E n) j] at ht
  have hp : (Functor.mapDerivedCategorySquareIso
      (comparisonFiniteOrdinaryPull l E b j n).symm).hom =
        (Functor.mapDerivedCategorySquareIso
          (comparisonFiniteOrdinaryPull l E b j n)).inv := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  have ho : (Functor.mapDerivedCategorySquareIso
      (comparisonFiniteOrdinaryOpen l E b j n).symm).hom =
        (comparisonFiniteOpen l E b j n).inv := by
    simp only [comparisonFiniteOpen, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hp, ho] at ht
  simp only [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, comparisonFinitePull, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc, leftDerivedUpperStarIsoMapDerivedCategory]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact ht

-- Explicit comparison congruences are checked within this declaration.
private theorem invert_face {C : Type*} [Category C] {A B D E F G : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ G)
    (d : A ≅ E) (e : E ≅ F) (f : F ≅ G)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    c.inv ≫ b.inv ≫ a.inv = f.inv ≫ e.inv ≫ d.inv := by
  have he : a ≪≫ b ≪≫ c = d ≪≫ e ≪≫ f := Iso.ext h
  simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv he

-- Explicit comparison congruences are checked within this declaration.
private theorem rotate_face {C : Type*} [Category C] {A B D E F G : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ G)
    (d : A ≅ E) (e : E ≅ F) (f : F ≅ G)
    (h : f.hom ≫ c.inv ≫ b.inv = e.inv ≫ d.inv ≫ a.hom) :
    d.hom ≫ e.hom ≫ f.hom = a.hom ≫ b.hom ≫ c.hom := by
  apply (cancel_mono (c.inv ≫ b.inv)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

-- Normalize the unit equation before specializing to the derived categories.
private theorem unit_equation_of_homEquiv
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {X : C} {Y : D} {f : L.obj X ⟶ Y} {g : X ⟶ R.obj Y}
    (h : a.homEquiv X Y f = g) : a.unit.app X ≫ R.map f = g := by
  simpa only [Adjunction.homEquiv_unit] using h

-- Explicit comparison congruences are checked within this declaration.
private theorem native_open_unit_mate (A : Type u) [CommRing A]
    {U' U Z' Z : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {g : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g)
    (N : DerivedCategory (Sheaf (ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j').unit.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).leftDerivedFunctor.obj N) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j').leftDerivedFunctor.map
        ((leftDerivedOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq).hom.app N) =
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).leftDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app N) ≫
      (leftDerivedUpperStarSquareIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).inv.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj N) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have he := unit_mateEquiv
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction B j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction B j')
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso
      B sq).inv) N
  rw [mateEquiv_leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_inv] at he
  simpa only [B, leftDerivedOpenImmersionLowerShriekBaseChangeIso,
    leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    TwoSquare.mk, Functor.comp_obj, Functor.id_obj,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc] using he.symm

-- Explicit comparison congruences are checked within this declaration.
private theorem inverse_pull_square (b : Base l E)
    {U' U T' T : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} (sq : IsPullback h j' j g) (n : ℕ)
    (M : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b U' n).map
        ((leftDerivedUpperStarSquareIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq.toCommSq).inv.app M) ≫
      (comparisonFinitePull l E b j' n).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) g).leftDerivedFunctor.obj M) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) j').map
        ((comparisonFinitePull l E b g n).hom.app M) =
    (comparisonFinitePull l E b h n).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).leftDerivedFunctor.obj M) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) h).map
        ((comparisonFinitePull l E b j n).hom.app M) ≫
      (proEtaleConstantRingPullbackComposition j' g (R l E n) ≪≫
        eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
          sq.w.symm) ≪≫
        (proEtaleConstantRingPullbackComposition h j (R l E n)).symm).inv.app
          ((comparisonFiniteRealization l E b T n).obj M) := by
  have he := invert_face
    ((proEtaleConstantRingDerivedPullback (R l E n) j').mapIso
      (Iso.app (comparisonFinitePull l E b g n).symm M))
    (Iso.app (comparisonFinitePull l E b j' n).symm
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) g).leftDerivedFunctor.obj M))
    ((comparisonFiniteRealization l E b U' n).mapIso
      (Iso.app (leftDerivedUpperStarSquareIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq.toCommSq) M))
    (Iso.app (proEtaleConstantRingPullbackComposition j' g (R l E n) ≪≫
      eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
        sq.w.symm) ≪≫
      (proEtaleConstantRingPullbackComposition h j (R l E n)).symm)
      ((comparisonFiniteRealization l E b T n).obj M))
    ((proEtaleConstantRingDerivedPullback (R l E n) h).mapIso
      (Iso.app (comparisonFinitePull l E b j n).symm M))
    (Iso.app (comparisonFinitePull l E b h n).symm
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).leftDerivedFunctor.obj M))
    (by
      have HC := strictFinitePullbackSquareCoherence l E b sq n M
      simp only [Iso.app, Functor.mapIso_hom, Iso.symm_hom, Iso.symm_inv]
      exact HC)
  simp only [Iso.app, Functor.mapIso_inv,
    Iso.symm_hom, Iso.symm_inv] at he
  exact he

-- Explicit comparison congruences are checked within this declaration.
private theorem open_scalar_from_comparisons
    {C C' D D' E E' F F' : Type*}
    [Category C] [Category C'] [Category D] [Category D']
    [Category E] [Category E'] [Category F] [Category F']
    {L : C ⥤ D} {J : D ⥤ C} {L' : C' ⥤ D'} {J' : D' ⥤ C'}
    {N : E ⥤ F} {R : F ⥤ E} {N' : E' ⥤ F'} {R' : F' ⥤ E'}
    {H : C ⥤ C'} {He : E ⥤ E'} {G : D ⥤ D'} {Ge : F ⥤ F'}
    {S : C ⥤ E} {S' : C' ⥤ E'} {Q : D ⥤ F} {Q' : D' ⥤ F'}
    (eg : Q ⋙ Ge ≅ G ⋙ Q') (eh : S ⋙ He ≅ H ⋙ S')
    (ej : Q ⋙ R ≅ J ⋙ S) (ej' : Q' ⋙ R' ≅ J' ⋙ S')
    (a : L ⊣ J) (a' : L' ⊣ J') (b : N ⊣ R) (b' : N' ⊣ R')
    (c : J ⋙ H ≅ G ⋙ J') (ce : R ⋙ He ≅ Ge ⋙ R')
    (i : S ⋙ N ⟶ L ⋙ Q) (i' : S' ⋙ N' ⟶ L' ⋙ Q')
    (d : H ⋙ L' ⟶ L ⋙ G) (de : He ⋙ N' ⟶ N ⋙ Ge)
    (hi : ∀ M, b.unit.app (S.obj M) ≫ R.map (i.app M) =
      S.map (a.unit.app M) ≫ ej.inv.app (L.obj M))
    (hi' : ∀ M, b'.unit.app (S'.obj M) ≫ R'.map (i'.app M) =
      S'.map (a'.unit.app M) ≫ ej'.inv.app (L'.obj M))
    (hd : ∀ M, a'.unit.app (H.obj M) ≫ J'.map (d.app M) =
      H.map (a.unit.app M) ≫ c.hom.app (L.obj M))
    (hde : ∀ M, b'.unit.app (He.obj M) ≫ R'.map (de.app M) =
      He.map (b.unit.app M) ≫ ce.hom.app (N.obj M))
    (hcube : ∀ K, S'.map (c.hom.app K) ≫ ej'.inv.app (G.obj K) ≫
      R'.map (eg.inv.app K) =
      eh.inv.app (J.obj K) ≫ He.map (ej.inv.app K) ≫ ce.hom.app (Q.obj K))
    (M : C) :
    N'.map (eh.inv.app M) ≫ de.app (S.obj M) ≫ Ge.map (i.app M) =
      i'.app (H.obj M) ≫ Q'.map (d.app M) ≫ eg.inv.app (L.obj M)  := by
  exact Adjunction.openScalar_exchange_of_unit a a' b b' H He G Ge S S' Q Q'
    eg eh ej ej' c ce i i' d de hi hi' hd hde hcube M

-- Explicit comparison congruences are checked within this declaration.
private theorem open_exchange_inverse (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    {U' U T' T : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ)
    (N : DerivedCategory (Sheaf (ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (sfIntrinsicDerivedOpen (R l E n) j').map
        ((comparisonFinitePull l E b h n).hom.app N) ≫
      (levels.openExchange h j' j g sq n).inv.app
        ((comparisonFiniteRealization l E b U n).obj N) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) g).map
        ((comparisonFiniteOpen l E b j n).inv.app N) =
    (comparisonFiniteOpen l E b j' n).inv.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) h).leftDerivedFunctor.obj N) ≫
      (comparisonFiniteRealization l E b T' n).map
        ((leftDerivedOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq).hom.app N) ≫
      (comparisonFinitePull l E b g n).hom.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).mapDerivedCategory.obj N) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))
  -- Share the converted mate and cube proofs so the kernel checks their conversions once.
  have H := open_scalar_from_comparisons
    (comparisonFinitePull l E b g n).symm (comparisonFinitePull l E b h n).symm
    (comparisonFinitePull l E b j n).symm (comparisonFinitePull l E b j' n).symm
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction B j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction B j')
    (comparisonLevelOpenAdjunction l E b j n)
    (comparisonLevelOpenAdjunction l E b j' n)
    (leftDerivedUpperStarSquareIso B sq.toCommSq).symm
    (proEtaleConstantRingPullbackComposition j' g (R l E n) ≪≫
      eqToIso (congrArg (fun a ↦ proEtaleConstantRingDerivedPullback (R l E n) a)
        sq.w.symm) ≪≫
      (proEtaleConstantRingPullbackComposition h j (R l E n)).symm).symm
    (comparisonFiniteOpen l E b j n).inv (comparisonFiniteOpen l E b j' n).inv
    (leftDerivedOpenImmersionLowerShriekBaseChangeIso B sq).hom
    (levels.openExchange h j' j g sq n).inv
    (by
      intro M
      have HU := strict_finite_open_unit l E b j n M
      simp only [B, Iso.symm_inv, Functor.comp_obj]
      exact HU) (by
      intro M
      have HU := strict_finite_open_unit l E b j' n M
      simp only [B, Iso.symm_inv, Functor.comp_obj]
      exact HU)
    (by
      as_aux_lemma =>
        intro M
        have HU := native_open_unit_mate (R l E n) sq M
        simp only [B, Iso.symm_hom, Functor.comp_obj]
        exact HU)
    (fun K ↦ by
      as_aux_lemma =>
        have he := unit_equation_of_homEquiv (comparisonLevelOpenAdjunction l E b j' n)
          (levels.openExchange_mate h j' j g sq n K)
        simp only [Iso.symm_hom, Iso.trans_inv,
          Iso.symm_inv, NatTrans.comp_app, Category.assoc,
          eqToIso.inv, Functor.comp_obj, Functor.id_obj] at he ⊢
        run_tac Lean.Elab.Tactic.withMainContext do
          let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `he) none
          exactByConversion h)
    (by
      as_aux_lemma =>
        intro M
        have HC := inverse_pull_square l E b sq n M
        simp only [B, Iso.symm_hom, Iso.symm_inv, Functor.comp_obj]
        run_tac Lean.Elab.Tactic.withMainContext do
          let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `HC) none
          exactByConversion h) N
  simp only [B, Iso.symm_inv, Functor.comp_obj] at H
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
    exactByConversion h

-- Explicit comparison congruences are checked within this declaration.
/-- Fixed-scalar realization preserves the normalized open exchange.
Source: blueprint operations proof (2), finite open exchange face.
(blueprint: new-lem-sp-strict-finite-open-exchange-face).

Proof: transpose the inverse of both exchange isomorphisms by the normalized
open adjunction. The open comparison is localization of the realization unit,
and the pullback comparison preserves the ordinary adjunction units. The two
transposes are therefore the horizontal pullback of the open unit followed by
the same canonical pullback-square compositor. Use openExchange_mate to identify
the intrinsic transpose and the native open base-change mate formula to identify
the other. Injectivity of the adjunction Hom bijection gives equality of the
inverse exchange words. Cancel their isomorphisms to obtain the forward face.
The argument uses exact localization on arbitrary unbounded objects and also
covers empty opens. -/
theorem strictFiniteOpenExchangeFace (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    {U' U T' T : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b T' n).map
        ((leftDerivedOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) sq).inv.app N) ≫
      (comparisonFiniteOpen l E b j' n).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          h).leftDerivedFunctor.obj N) ≫
      (sfIntrinsicDerivedOpen (R l E n) j').map
        ((comparisonFinitePull l E b h n).hom.app N) =
    (comparisonFinitePull l E b g n).hom.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).mapDerivedCategory.obj N) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) g).map
        ((comparisonFiniteOpen l E b j n).hom.app N) ≫
      (levels.openExchange h j' j g sq n).hom.app
        ((comparisonFiniteRealization l E b U n).obj N) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))
  have he := rotate_face
    (Iso.app (comparisonFinitePull l E b g n)
      ((openImmersionLowerShriek B j).mapDerivedCategory.obj N))
    ((proEtaleConstantRingDerivedPullback (R l E n) g).mapIso
      (Iso.app (comparisonFiniteOpen l E b j n) N))
    (Iso.app (levels.openExchange h j' j g sq n)
      ((comparisonFiniteRealization l E b U n).obj N))
    ((comparisonFiniteRealization l E b T' n).mapIso
      (Iso.app (leftDerivedOpenImmersionLowerShriekBaseChangeIso B sq).symm N))
    (Iso.app (comparisonFiniteOpen l E b j' n)
      ((upperStar B h).leftDerivedFunctor.obj N))
    ((sfIntrinsicDerivedOpen (R l E n) j').mapIso
      (Iso.app (comparisonFinitePull l E b h n) N))
    (open_exchange_inverse l E b o levels sq n N)
  simp only [B, Iso.app, Functor.mapIso_hom, Iso.symm_hom] at he
  run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `he) none
        exactByConversion h

end AlgebraicGeometry.ProEtale.SpTowerShriek
