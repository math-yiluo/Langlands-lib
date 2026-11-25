/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-!
# Canonical tensor composition at the coefficient unit

The comparison coordinates are the original constructed compactification and
adjunction comparisons. The theorem isolates the equality in clause 4 of
cohomological smoothness, independently of invertibility, base change and Dctf.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The compact-support composition comparison, constructed from the compatible
compactifications and the common-refinement comparisons, rather than chosen from a
Nonempty assertion. The compatible compactification is the closure of X in the product
of the chosen compactifications of g and fg.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, clause 4 and proof Step 9;
proposition-composition-base-change-rf-shriek--1, triangle construction
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def smoothCompactSupportCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g :=
  let c := HasCompactification.compactification g
  let b := (HasCompactification.compactification (f ≫ g)).ofComp c
  (Etale.rightDerivedLowerShriekIso Λ (c.comp b)).symm ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso Λ c b).symm ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso Λ b.restrict) _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIso Λ c)

/-- The adjunction-compatible exceptional composition comparison. Its counit is
ε_g followed in adjunction order by g_! ε_f, through the displayed compact-support
comparison, since this is rightAdjointUniq for precisely that composite adjunction.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, clause 4, proof Step 9
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def smoothExceptionalCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    Etale.rightDerivedUpperShriek Λ (f ≫ g) ≅
      Etale.rightDerivedUpperShriek Λ g ⋙
        Etale.rightDerivedUpperShriek Λ f :=
  Adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction Λ (f ≫ g)).ofNatIsoLeft
      (smoothCompactSupportCompIso Λ f g))
    ((Etale.rightDerivedUpperShriekAdjunction Λ f).comp
      (Etale.rightDerivedUpperShriekAdjunction Λ g))

/-- The specified dualizing comparison q = θ_(f,ω_g) followed by c_Λ⁻¹.
Its invertibility is asserted below; its data use only the existing tensor mate
and the adjunction-induced composition comparison.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, clause 4, proof Step 9
(blueprint: proposition-exceptional-inverse-image-smooth-morphism). -/
noncomputable def smoothDualizingCompMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex Λ f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex Λ g)) ⟶
      Etale.dualizingComplex Λ (f ≫ g) :=
  Etale.dualizingComplexTensorMap Λ f (Etale.dualizingComplex Λ g) ≫
    (smoothExceptionalCompIso Λ f g).inv.app (𝟙_ _)

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
attribute [local irreducible] Etale.projectionMapOfCompactification Etale.projectionMap
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  Etale.openImmersionLowerShriek Etale.upperStar Etale.lowerStar
attribute [local implicit_reducible] Etale.rightDerivedLowerShriek
attribute [local implicit_reducible] smoothDualizingCompMap smoothExceptionalCompIso
  Etale.dualizingComplexTensorMap Etale.dualizingComplex
  Etale.lowerShriekRightAdjointUnitTensorMap Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

-- Explicit congruence keeps proof-irrelevant instance parameters from forcing the
-- kernel to unfold the derived-category constructions. The structural comparison
-- follows EtaleOpenInjectiveLerayEdge and projectionMapAssociativity in the source library.
private meta def instanceCongrToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- The congruence method of HigherDirectImageRawTransitionToHomCore, which also reads through
-- `let`s and `(𝟭 _).obj`. Build congruence proofs before reducing the large derived-category
-- objects, so that the kernel only meets proof irrelevance at the leaves.
private meta def instanceCongrHEq
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      let a := a.consumeMData
      let b := b.consumeMData
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' =>
          if (e'.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
              e'.isAppOfArity ``CategoryTheory.Functor.map 8) &&
              (e'.getArg! 4).isAppOfArity ``CategoryTheory.Functor.id 2 then
            e'.getAppArgs.back!
          else e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← instanceCongrHEq cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← instanceCongrHEq cache pairs n type type'
          let htype ← instanceCongrToEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← instanceCongrHEq cache (pairs.push (x, y, hxy)) n
                  (body.instantiate1 x) (body'.instantiate1 y)
                let h ← Lean.Meta.mkLambdaFVars #[x, y, hxy] h
                Lean.Meta.mkAppM ``Function.hfunext #[htype, h]
      let expandProjection (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let fn := e.getAppFn
        let .proj typeName index major := fn | return e
        let info := Lean.getStructureInfo (← Lean.getEnv) typeName
        let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
        return Lean.mkAppN p e.getAppArgs
      let a' ← expandProjection a
      let b' ← expandProjection b
      if a != a' || b != b' then
        return ← instanceCongrHEq cache pairs n a' b'
      let af := a.getAppFn.consumeMData
      let bf := b.getAppFn.consumeMData
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if af.isConstOf ``CategoryTheory.Preadditive.mk &&
          bf.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Preadditive.mk &&
          af.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if af.isConstOf ``CategoryTheory.Functor.mk &&
          bf.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Functor.mk &&
          af.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      let sameHead ← if af == bf then pure true else
        if af.isConst && bf.isConst && af.constName! == bf.constName! then
          Lean.Meta.isDefEq af bf
        else pure false
      if sameHead && aa.size ≥ 4 && ba.size ≥ 4 &&
          (af.isConstOf ``CategoryTheory.Functor.obj ||
            af.isConstOf ``CategoryTheory.Functor.map ||
            af.isConstOf ``CategoryTheory.NatTrans.app) then
        let sameDomain ← Lean.Meta.isDefEq aa[0]! ba[0]!
        let sameCodomain ← Lean.Meta.isDefEq aa[2]! ba[2]!
        if !sameDomain || !sameCodomain then
          let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
            let some e' ← Lean.Meta.withTransparency .instances
                (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
            let some f ← Lean.Meta.withTransparency .all
                (Lean.Meta.reduceProj? e'.getAppFn) | return none
            let e'' := Lean.mkAppN f e'.getAppArgs
            if e'' == e then return none
            return some e''
          if let some a' ← reduceComponent a then
            return ← instanceCongrHEq cache pairs n a' b
          if let some b' ← reduceComponent b then
            return ← instanceCongrHEq cache pairs n a b'
      if !sameHead || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← instanceCongrHEq cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← instanceCongrHEq cache pairs n a b'
        let reduceProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          if e''.getAppFn.isProj then
            let .proj typeName index major := e''.getAppFn | return none
            let info := Lean.getStructureInfo (← Lean.getEnv) typeName
            let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
            let e''' := Lean.mkAppN p e''.getAppArgs
            if e''' == e then return none
          return some e''
        if ← isProjection af then
          if let some a' ← reduceProjection a then
            return ← instanceCongrHEq cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← instanceCongrHEq cache pairs n a b'
        throwError "different congruence heads: {a} versus {b}"
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
          let functor := args[args.size - 2]!
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
      if a != a' || b != b' then
        return ← instanceCongrHEq cache pairs n a' b'
      let build : Lean.MetaM Lean.Expr := do
        let mut first := 0
        while first < aa.size && aa[first]! == ba[first]! do
          first := first + 1
        let f := Lean.mkAppN af (aa.extract 0 first)
        let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
        let mut args := #[]
        for i in [first:aa.size] do
          let h ← instanceCongrHEq cache pairs n aa[i]! ba[i]!
          let h ← if ct.argKinds[i - first]! == .eq then
            instanceCongrToEq h else pure h
          args := args.push aa[i]! |>.push ba[i]! |>.push h
        return Lean.mkAppN ct.proof args
      try build catch err =>
        -- Equal applications can expose their functor parameters differently.
        -- Reduce a component projection before trying to compare those parameters.
        let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          return some e''
        if let some a' ← reduceComponent a then
          return ← instanceCongrHEq cache pairs n a' b
        if let some b' ← reduceComponent b then
          return ← instanceCongrHEq cache pairs n a b'
        throw err
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

-- Establish the tensor normalization at the functor level, before it is
-- applied to objects involving compactly supported derived images.
private theorem derivedTensorCanonical
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u}) :
    Etale.derivedTensor B X = curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology B)) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.Elab.Tactic.getMainTarget
    let some (_, lhs, rhs) := target.eq? | throwError "expected a tensor equality"
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← instanceCongrHEq cache #[] 200 lhs rhs
    let proof ← Lean.Meta.mkAppM ``eq_of_heq #[h]
    (← Lean.Elab.Tactic.getMainGoal).assign proof

open Lean Elab Tactic Meta in
local elab "exact_congr_type " h:term : tactic => withMainContext do
  let proof ← elabTerm h none
  let target ← instantiateMVars (← getMainTarget)
  let proofType ← instantiateMVars (← inferType proof)
  let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
  let ds := (← getLCtx).decls.toList.filterMap id
  if let some dB := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `B) then
    for d in ds do
      if d.type.isAppOf ``AlgebraicGeometry.Scheme then
        let h ← mkAppM ``derivedTensorCanonical #[dB.toExpr, d.toExpr]
        let some (_, lhs, rhs) := (← inferType h).eq? | throwError "expected tensor equality"
        let he ← mkAppM ``heq_of_eq #[h]
        cache.modify fun m => m.insert (lhs, rhs) he
  let he ← instanceCongrHEq cache #[] 200 proofType target
  let e ← mkAppM ``eq_of_heq #[he]
  (← getMainGoal).assign (← mkAppM ``Eq.mp #[e, proof])

private theorem transportProjectionComp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (TE : E ⥤ E ⥤ E)
    {Ff : D ⥤ C} {Fg : E ⥤ D} {Fh : E ⥤ C}
    {Lf Lf₀ : C ⥤ D} {Lg Lg₀ : D ⥤ E} {Lh Lh₀ : C ⥤ E}
    (πf : ∀ M N, (TD.obj (Lf.obj M)).obj N ⟶ Lf.obj ((TC.obj M).obj (Ff.obj N)))
    (πf₀ : ∀ M N, (TD.obj (Lf₀.obj M)).obj N ⟶ Lf₀.obj ((TC.obj M).obj (Ff.obj N)))
    (πg : ∀ M N, (TE.obj (Lg.obj M)).obj N ⟶ Lg.obj ((TD.obj M).obj (Fg.obj N)))
    (πg₀ : ∀ M N, (TE.obj (Lg₀.obj M)).obj N ⟶ Lg₀.obj ((TD.obj M).obj (Fg.obj N)))
    (πh : ∀ M N, (TE.obj (Lh.obj M)).obj N ⟶ Lh.obj ((TC.obj M).obj (Fh.obj N)))
    (πh₀ : ∀ M N, (TE.obj (Lh₀.obj M)).obj N ⟶ Lh₀.obj ((TC.obj M).obj (Fh.obj N)))
    (γ : ∀ N, Fh.obj N ⟶ Ff.obj (Fg.obj N))
    (a : Lf₀ ≅ Lf) (b : Lg₀ ≅ Lg) (c : Lh₀ ≅ Lh)
    (t : Lf₀ ⋙ Lg₀ ≅ Lh₀)
    (hf : ∀ M N, πf₀ M N ≫ a.hom.app _ = (TD.flip.obj N).map (a.hom.app M) ≫ πf M N)
    (hg : ∀ M N, πg₀ M N ≫ b.hom.app _ = (TE.flip.obj N).map (b.hom.app M) ≫ πg M N)
    (hh : ∀ M N, πh₀ M N ≫ c.hom.app _ = (TE.flip.obj N).map (c.hom.app M) ≫ πh M N)
    (hπg₀ : ∀ {M M'} (φ : M ⟶ M') N,
      (TE.flip.obj N).map (Lg₀.map φ) ≫ πg₀ M' N =
        πg₀ M N ≫ Lg₀.map ((TD.flip.obj (Fg.obj N)).map φ))
    (ht : ∀ M N, πg₀ (Lf₀.obj M) N ≫ Lg₀.map (πf₀ M (Fg.obj N)) ≫
      t.hom.app _ = (TE.flip.obj N).map (t.hom.app M) ≫ πh₀ M N ≫ Lh₀.map ((TC.obj M).map (γ N))) :
    let e := c.symm ≪≫ t.symm ≪≫ Functor.isoWhiskerRight a Lg₀ ≪≫
      Functor.isoWhiskerLeft Lf b
    ∀ M N, (TE.flip.obj N).map (e.hom.app M) ≫ πg (Lf.obj M) N ≫
      Lg.map (πf M (Fg.obj N)) = πh M N ≫
        e.hom.app ((TC.obj M).obj (Fh.obj N)) ≫
        Lg.map (Lf.map ((TC.obj M).map (γ N))) := by
  dsimp only
  intro M N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hg (Lf.obj M) N), reassoc_of% (hπg₀ (a.hom.app M) N)]
  rw [← b.hom.naturality (πf M (Fg.obj N))]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [← Lg₀.map_comp_assoc, ← hf, Lg₀.map_comp]
  have ht' := ht M N
  rw [← cancel_epi ((TE.flip.obj N).map (t.inv.app M))] at ht'
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app] at ht'
  rw [(TE.flip.obj N).map_id, Category.id_comp] at ht'
  rw [← cancel_mono (t.inv.app _)] at ht'
  simp only [Category.assoc, Iso.hom_inv_id_app] at ht'
  simp only [Category.assoc]
  rw [reassoc_of% ht']
  have hh' := hh M N
  rw [← cancel_epi ((TE.flip.obj N).map (c.inv.app M)), ← cancel_mono (c.inv.app _)] at hh'
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app] at hh'
  rw [(TE.flip.obj N).map_id, Category.id_comp] at hh'
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hh'
  rw [reassoc_of% hh']
  rw [reassoc_of% (t.inv.naturality ((TC.obj M).map (γ N)))]
  rw [← Lg₀.map_comp_assoc, a.hom.naturality ((TC.obj M).map (γ N)), Lg₀.map_comp,
    ← b.hom.naturality (Lf.map ((TC.obj M).map (γ N)))]
  simp only [Category.assoc]

private theorem invIsoHom {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) :
    inv e.hom = e.inv := by
  apply IsIso.inv_eq_of_hom_inv_id
  exact e.hom_inv_id

private theorem unitTensorAssoc
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ M N, L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [hπiso : ∀ M N, IsIso (π M N)]
    (hπ : ∀ {M M'} (φ : M ⟶ M') N,
      L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (δ : ∀ N N', F.obj (N ⊗ N') ⟶ F.obj N ⊗ F.obj N')
    [∀ N N', IsIso (δ N N')]
    (hassoc : ∀ M N N', π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
      L.map (α_ M _ _).hom = (α_ _ N N').hom ≫ π M (N ⊗ N') ≫
        L.map (M ◁ δ N N')) (N N' : D) :
    (adj.projectionTensorMap π (𝟙_ D) N ≫ R.map (λ_ N).hom) ▷ F.obj N' ≫
      adj.projectionTensorMap π N N' =
    (α_ (R.obj (𝟙_ D)) (F.obj N) (F.obj N')).hom ≫
      R.obj (𝟙_ D) ◁ inv (δ N N') ≫
      adj.projectionTensorMap π (𝟙_ D) (N ⊗ N') ≫ R.map (λ_ (N ⊗ N')).hom := by
  rw [comp_whiskerRight, Category.assoc,
    adj.projectionTensorMap_naturality_left π hπ (λ_ N).hom N']
  have h := congrArg (fun z ↦ z ≫ R.map (λ_ (N ⊗ N')).hom)
    (adj.projectionTensorMap_assoc π hπ δ hassoc (𝟙_ D) N N')
  simpa only [Category.assoc, ← R.map_comp, leftUnitor_tensor_hom,
    Iso.hom_inv_id_assoc] using h

section ProjectionComponents

variable
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] [Etale.UpperStarPreservesFlat B]
  {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}}

-- These signatures normalize only object components. Comparing the entire
-- bifunctors would also compare their large derived-functor map constructions.
private noncomputable def compactProjectionPoint {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((Etale.derivedTensor B Y).obj
      ((Etale.rightDerivedLowerShriekOfCompactification B c).obj M)).obj N ⟶
      (Etale.rightDerivedLowerShriekOfCompactification B c).obj
        (((Etale.derivedTensor B X).obj M).obj
          ((Etale.upperStar B f).leftDerivedFunctor.obj N)) :=
  ((Etale.projectionMapOfCompactification B c).app M).app N

private noncomputable def chosenProjectionPoint (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((Etale.derivedTensor B Y).obj ((Etale.rightDerivedLowerShriek B f).obj M)).obj N ⟶
      (Etale.rightDerivedLowerShriek B f).obj
        (((Etale.derivedTensor B X).obj M).obj
          ((Etale.upperStar B f).leftDerivedFunctor.obj N)) :=
  ((Etale.projectionMap B f).app M).app N

private theorem compactProjectionPoint_naturality {f : X ⟶ Y} (c : Compactification f)
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology B)} (φ : M ⟶ M')
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((Etale.derivedTensor B Y).map
      ((Etale.rightDerivedLowerShriekOfCompactification B c).map φ)).app N ≫
        compactProjectionPoint B c M' N =
      compactProjectionPoint B c M N ≫
        (Etale.rightDerivedLowerShriekOfCompactification B c).map
          (((Etale.derivedTensor B X).map φ).app
            ((Etale.upperStar B f).leftDerivedFunctor.obj N)) := by
  have hn := Etale.projectionMapOfCompactification_naturality B c φ (𝟙 N)
  rw [((Etale.derivedTensor B Y).obj
    ((Etale.rightDerivedLowerShriekOfCompactification B c).obj M')).map_id,
    (Etale.upperStar B f).leftDerivedFunctor.map_id,
    ((Etale.derivedTensor B X).obj M').map_id] at hn
  simpa only [compactProjectionPoint, Category.id_comp, Category.comp_id] using hn

end ProjectionComponents

private def etaleProjectionCompatible
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] [Etale.UpperStarPreservesFlat B]
  {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (e : Etale.rightDerivedLowerShriek B (f ≫ g) ≅
      Etale.rightDerivedLowerShriek B f ⋙ Etale.rightDerivedLowerShriek B g) : Prop :=
  Adjunction.ProjectionCompCompatible
    (fun M N ↦ ((Etale.projectionMap B f).app M).app N)
    (fun M N ↦ ((Etale.projectionMap B g).app M).app N)
    (fun M N ↦ ((Etale.projectionMap B (f ≫ g)).app M).app N)
    (fun N ↦ (Etale.leftDerivedUpperStarComp B f g).hom.app N) e

private theorem projectionCompatibleOfBifunctor
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    {Ff : D ⥤ C} {Fg : E ⥤ D} {Fh : E ⥤ C}
    {Lf : C ⥤ D} {Lg : D ⥤ E} {Lh : C ⥤ E}
    (πf : ∀ M N, Lf.obj M ⊗ N ⟶ Lf.obj (M ⊗ Ff.obj N))
    (πg : ∀ M N, Lg.obj M ⊗ N ⟶ Lg.obj (M ⊗ Fg.obj N))
    (πh : ∀ M N, Lh.obj M ⊗ N ⟶ Lh.obj (M ⊗ Fh.obj N))
    (γ : ∀ N, Fh.obj N ⟶ Ff.obj (Fg.obj N))
    (e : Lh ≅ Lf ⋙ Lg)
    (h : ∀ M N,
      ((curriedTensor E).flip.obj N).map (e.hom.app M) ≫ πg (Lf.obj M) N ≫
        Lg.map (πf M (Fg.obj N)) =
      πh M N ≫ e.hom.app (((curriedTensor C).obj M).obj (Fh.obj N)) ≫
        Lg.map (Lf.map (((curriedTensor C).obj M).map (γ N)))) :
    Adjunction.ProjectionCompCompatible πf πg πh γ e := by
  constructor
  intro M N
  exact h M N

private theorem etaleProjectionTransport
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] [Etale.UpperStarPreservesFlat B]
  {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (a : Etale.rightDerivedLowerShriekOfCompactification B cf ≅
      Etale.rightDerivedLowerShriek B f)
    (b : Etale.rightDerivedLowerShriekOfCompactification B cg ≅
      Etale.rightDerivedLowerShriek B g)
    (c : Etale.rightDerivedLowerShriekOfCompactification B ch ≅
      Etale.rightDerivedLowerShriek B (f ≫ g))
    (t : Etale.rightDerivedLowerShriekOfCompactification B cf ⋙
      Etale.rightDerivedLowerShriekOfCompactification B cg ≅
      Etale.rightDerivedLowerShriekOfCompactification B ch)
    (hf : ∀ M N,
      ((Etale.projectionMapOfCompactification B cf).app M).app N ≫
        a.hom.app (((Etale.derivedTensor B X).obj M).obj
          ((Etale.upperStar B f).leftDerivedFunctor.obj N)) =
      ((Etale.derivedTensor B Y).map (a.hom.app M)).app N ≫
        ((Etale.projectionMap B f).app M).app N)
    (hg : ∀ M N,
      ((Etale.projectionMapOfCompactification B cg).app M).app N ≫
        b.hom.app (((Etale.derivedTensor B Y).obj M).obj
          ((Etale.upperStar B g).leftDerivedFunctor.obj N)) =
      ((Etale.derivedTensor B Z).map (b.hom.app M)).app N ≫
        ((Etale.projectionMap B g).app M).app N)
    (hh : ∀ M N,
      ((Etale.projectionMapOfCompactification B ch).app M).app N ≫
        c.hom.app (((Etale.derivedTensor B X).obj M).obj
          ((Etale.upperStar B (f ≫ g)).leftDerivedFunctor.obj N)) =
      ((Etale.derivedTensor B Z).map (c.hom.app M)).app N ≫
        ((Etale.projectionMap B (f ≫ g)).app M).app N)
    (ht : ∀ M N,
      ((Etale.projectionMapOfCompactification B cg).app
        ((Etale.rightDerivedLowerShriekOfCompactification B cf).obj M)).app N ≫
      (Etale.rightDerivedLowerShriekOfCompactification B cg).map
        (((Etale.projectionMapOfCompactification B cf).app M).app
          ((Etale.upperStar B g).leftDerivedFunctor.obj N)) ≫
        t.hom.app (((Etale.derivedTensor B X).obj M).obj
          ((Etale.upperStar B f).leftDerivedFunctor.obj
            ((Etale.upperStar B g).leftDerivedFunctor.obj N))) =
      ((Etale.derivedTensor B Z).map (t.hom.app M)).app N ≫
        ((Etale.projectionMapOfCompactification B ch).app M).app N ≫
        (Etale.rightDerivedLowerShriekOfCompactification B ch).map
          (((Etale.derivedTensor B X).obj M).map
            ((Etale.leftDerivedUpperStarComp B f g).hom.app N))) :
    etaleProjectionCompatible B f g
      (c.symm ≪≫ t.symm ≪≫ Functor.isoWhiskerRight a _ ≪≫ Functor.isoWhiskerLeft _ b) := by
  unfold etaleProjectionCompatible
  apply projectionCompatibleOfBifunctor
    (Ff := (Etale.upperStar B f).leftDerivedFunctor)
    (Fg := (Etale.upperStar B g).leftDerivedFunctor)
    (Fh := (Etale.upperStar B (f ≫ g)).leftDerivedFunctor)
    (Lf := Etale.rightDerivedLowerShriek B f)
    (Lg := Etale.rightDerivedLowerShriek B g)
    (Lh := Etale.rightDerivedLowerShriek B (f ≫ g))
  intro M₀ N₀
  dsimp only [Functor.flip_obj_map]
  exact_congr_type transportProjectionComp
    (Etale.derivedTensor B X) (Etale.derivedTensor B Y) (Etale.derivedTensor B Z)
    (C := DerivedCategory (Sheaf X.smallEtaleTopology B))
    (D := DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (E := DerivedCategory (Sheaf Z.smallEtaleTopology B))
    (Ff := (Etale.upperStar B f).leftDerivedFunctor)
    (Fg := (Etale.upperStar B g).leftDerivedFunctor)
    (Fh := (Etale.upperStar B (f ≫ g)).leftDerivedFunctor)
    (Lf := Etale.rightDerivedLowerShriek B f)
    (Lg := Etale.rightDerivedLowerShriek B g)
    (Lh := Etale.rightDerivedLowerShriek B (f ≫ g))
    (Lf₀ := Etale.rightDerivedLowerShriekOfCompactification B cf)
    (Lg₀ := Etale.rightDerivedLowerShriekOfCompactification B cg)
    (Lh₀ := Etale.rightDerivedLowerShriekOfCompactification B ch)
    (πf := chosenProjectionPoint B f)
    (πg := chosenProjectionPoint B g)
    (πh := chosenProjectionPoint B (f ≫ g))
    (γ := fun N ↦ (Etale.leftDerivedUpperStarComp B f g).hom.app N)
    (πf₀ := compactProjectionPoint B cf)
    (πg₀ := compactProjectionPoint B cg)
    (πh₀ := compactProjectionPoint B ch)
    (a := a) (b := b) (c := c) (t := t)
    (by
      intro M N
      dsimp only [Functor.flip_obj_map, compactProjectionPoint, chosenProjectionPoint]
      exact_congr_type hf M N)
    (by
      intro M N
      dsimp only [Functor.flip_obj_map, compactProjectionPoint, chosenProjectionPoint]
      exact_congr_type hg M N)
    (by
      intro M N
      dsimp only [Functor.flip_obj_map, compactProjectionPoint, chosenProjectionPoint]
      exact_congr_type hh M N)
    (by
      intro M M' φ N
      dsimp only [Functor.flip_obj_map]
      exact compactProjectionPoint_naturality B cg φ N)
    (by
      intro M N
      dsimp only [Functor.flip_obj_map, compactProjectionPoint]
      exact_congr_type ht M N) M₀ N₀

private theorem smoothProjectionCompCompatible
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    etaleProjectionCompatible (ModuleCat.{u + 1} A) f g
      (smoothCompactSupportCompIso A f g) := by
  let c := HasCompactification.compactification g
  let b := (HasCompactification.compactification (f ≫ g)).ofComp c
  exact etaleProjectionTransport (ModuleCat.{u + 1} A) f g b.restrict c (c.comp b)
    (Etale.rightDerivedLowerShriekIso A b.restrict) (Etale.rightDerivedLowerShriekIso A c)
    (Etale.rightDerivedLowerShriekIso A (c.comp b))
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso A c b)
    (Etale.projectionMapOfCompactification_rightDerivedLowerShriekIso A b.restrict)
    (Etale.projectionMapOfCompactification_rightDerivedLowerShriekIso A c)
    (Etale.projectionMapOfCompactification_rightDerivedLowerShriekIso A (c.comp b))
    (Etale.projectionMapOfCompactification_tower_comp A f g c b)

private theorem unitTensorNaturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ M N, L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [hπiso : ∀ M N, IsIso (π M N)]
    (hπ : ∀ M {N N'} (φ : N ⟶ N'),
      L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ F.map φ))
    {N N' : D} (φ : N ⟶ N') :
    R.obj (𝟙_ D) ◁ F.map φ ≫
      (adj.projectionTensorMap π (𝟙_ D) N' ≫ R.map (λ_ N').hom) =
    (adj.projectionTensorMap π (𝟙_ D) N ≫ R.map (λ_ N).hom) ≫ R.map φ := by
  rw [← Category.assoc, adj.projectionTensorMap_naturality_right π hπ,
    Category.assoc, ← R.map_comp, leftUnitor_naturality, R.map_comp, Category.assoc]

private theorem unitComposition
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    {Ff : D ⥤ C} {Fg : E ⥤ D} {Fh : E ⥤ C}
    {Rf : D ⥤ C} {Rg : E ⥤ D} {Rh : E ⥤ C}
    (τf : ∀ M N, Rf.obj M ⊗ Ff.obj N ⟶ Rf.obj (M ⊗ N))
    (τg : ∀ M N, Rg.obj M ⊗ Fg.obj N ⟶ Rg.obj (M ⊗ N))
    (τh : ∀ M N, Rh.obj M ⊗ Fh.obj N ⟶ Rh.obj (M ⊗ N))
    (θf : ∀ N, Rf.obj (𝟙_ D) ⊗ Ff.obj N ⟶ Rf.obj N)
    (θg : ∀ N, Rg.obj (𝟙_ E) ⊗ Fg.obj N ⟶ Rg.obj N)
    (θh : ∀ N, Rh.obj (𝟙_ E) ⊗ Fh.obj N ⟶ Rh.obj N)
    (hθg : ∀ N, θg N = τg (𝟙_ E) N ≫ Rg.map (λ_ N).hom)
    (hθh : ∀ N, θh N = τh (𝟙_ E) N ≫ Rh.map (λ_ N).hom)
    (δ : ∀ N N', Ff.obj (N ⊗ N') ⟶ Ff.obj N ⊗ Ff.obj N')
    [∀ N N', IsIso (δ N N')]
    (γ : Fh ⟶ Fg ⋙ Ff) (ρ : Rh ≅ Rg ⋙ Rf)
    (hc : ∀ M N, τh M N ≫ ρ.hom.app (M ⊗ N) =
      ρ.hom.app M ▷ Fh.obj N ≫ Rf.obj (Rg.obj M) ◁ γ.app N ≫
      τf (Rg.obj M) (Fg.obj N) ≫ Rf.map (τg M N))
    (ha : ∀ N N', θf N ▷ Ff.obj N' ≫ τf N N' =
      (α_ _ _ _).hom ≫ Rf.obj (𝟙_ D) ◁ inv (δ N N') ≫ θf (N ⊗ N'))
    (hn : ∀ {N N'} (φ : N ⟶ N'),
      Rf.obj (𝟙_ D) ◁ Ff.map φ ≫ θf N' = θf N ≫ Rf.map φ)
    (K : E) :
    (θf (Rg.obj (𝟙_ E)) ≫ ρ.inv.app (𝟙_ E)) ▷ Fh.obj K ≫ θh K ≫ ρ.hom.app K =
    (α_ _ _ _).hom ≫ Rf.obj (𝟙_ D) ◁
      (Ff.obj (Rg.obj (𝟙_ E)) ◁ γ.app K ≫ inv (δ _ _) ≫ Ff.map (θg K)) ≫
      θf (Rg.obj K) := by
  have hc' := hc (𝟙_ E) K
  have hnρ := ρ.hom.naturality (λ_ K).hom
  dsimp only [Functor.comp_map] at hnρ
  simp only [hθh, comp_whiskerRight, Category.assoc]
  rw [hnρ, reassoc_of% hc']
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id_app]
  rw [← whisker_exchange_assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  rw [reassoc_of% (ha (Rg.obj (𝟙_ E)) (Fg.obj K)),
    associator_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hn (θg K), hθg, Rf.map_comp]

private noncomputable abbrev exceptionalCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (e : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g) :
    Etale.rightDerivedUpperShriek Λ (f ≫ g) ≅
      Etale.rightDerivedUpperShriek Λ g ⋙ Etale.rightDerivedUpperShriek Λ f :=
  Adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction Λ (f ≫ g)).ofNatIsoLeft e)
    ((Etale.rightDerivedUpperShriekAdjunction Λ f).comp
      (Etale.rightDerivedUpperShriekAdjunction Λ g))

private theorem unitCompositionEtale
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (e : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g)
    (he : etaleProjectionCompatible (ModuleCat.{u + 1} Λ) f g e)
    (hassoc : Etale.ProjectionMapAssociativity (ModuleCat.{u + 1} Λ) f)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.dualizingComplexTensorMap Λ f (Etale.dualizingComplex Λ g) ≫
      (exceptionalCompIso Λ f g e).inv.app (𝟙_ _)) ▷
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ g)).leftDerivedFunctor.obj K ≫
      Etale.dualizingComplexTensorMap Λ (f ≫ g) K ≫
        (exceptionalCompIso Λ f g e).hom.app K =
      (α_ (Etale.dualizingComplex Λ f)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex Λ g))
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ g)).leftDerivedFunctor.obj K)).hom ≫
      (Etale.dualizingComplex Λ f) ◁
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex Λ g)) ◁
            (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom.app K ≫
          (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f
            (Etale.dualizingComplex Λ g)
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj K)).inv ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.map
            (Etale.dualizingComplexTensorMap Λ g K)) ≫
      Etale.dualizingComplexTensorMap Λ f
        ((Etale.rightDerivedUpperShriek Λ g).obj K)  := by
  rw [← invIsoHom (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f
    (Etale.dualizingComplex Λ g)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj K))]
  apply unitComposition
    (Ff := (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor)
    (Fg := (Etale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor)
    (Fh := (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ g)).leftDerivedFunctor)
    (Rf := Etale.rightDerivedUpperShriek Λ f)
    (Rg := Etale.rightDerivedUpperShriek Λ g)
    (Rh := Etale.rightDerivedUpperShriek Λ (f ≫ g))
    (τf := Etale.rightDerivedUpperShriekTensorMap f)
    (τg := Etale.rightDerivedUpperShriekTensorMap g)
    (τh := Etale.rightDerivedUpperShriekTensorMap (f ≫ g))
    (θf := Etale.dualizingComplexTensorMap Λ f)
    (θg := Etale.dualizingComplexTensorMap Λ g)
    (θh := Etale.dualizingComplexTensorMap Λ (f ≫ g))
    (δ := fun N N' ↦ (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f N N').hom)
    (γ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom)
    (ρ := exceptionalCompIso Λ f g e)
  case hc =>
    exact Etale.lowerShriekRightAdjointTensorMap_comp rfl _ _ _ e he
  case ha =>
    intro N N'
    exact unitTensorAssoc (hπiso := fun M N ↦ by
      let : IsIso ((Etale.projectionMap (ModuleCat.{u + 1} Λ) f).app M) :=
        NatIso.isIso_app_of_isIso (Etale.projectionMap (ModuleCat.{u + 1} Λ) f) M
      exact NatIso.isIso_app_of_isIso ((Etale.projectionMap (ModuleCat.{u + 1} Λ) f).app M) N)
      (Etale.rightDerivedUpperShriekAdjunction Λ f) _
      (Etale.projectionMap_app_app_naturality_left f) _
      hassoc.assoc N N'
  case hn =>
    intro N N' φ
    exact unitTensorNaturality (hπiso := fun M N ↦ by
      let : IsIso ((Etale.projectionMap (ModuleCat.{u + 1} Λ) f).app M) :=
        NatIso.isIso_app_of_isIso (Etale.projectionMap (ModuleCat.{u + 1} Λ) f) M
      exact NatIso.isIso_app_of_isIso ((Etale.projectionMap (ModuleCat.{u + 1} Λ) f).app M) N)
      (Etale.rightDerivedUpperShriekAdjunction Λ f) _
      (Etale.projectionMap_app_app_naturality_right f) φ
  case hθg => intro N; rfl
  case hθh => intro N; rfl

/-- Unit specialization of the canonical tensor-composition identity.
Proof: the compactification-tower projection identity is transported through the
three common-refinement comparisons. Naturality of projection maps under each
comparison gives ProjectionCompCompatible for smoothCompactSupportCompIso.
Apply lowerShriekRightAdjointTensorMap_comp with this compatibility and specialize
its first variable to the coefficient unit. Naturality of the adjoint comparison
cancels its inverse from q. The projectionTensorMap_assoc identity, naturality of
the tensor map in both variables, and the left-unitor identity then give precisely
the reassociated right-hand composite. This argument needs no smoothness or
invertibility of the dualizing object; it also applies to empty schemes and the
zero coefficient ring.
Source: blueprint proposition-exceptional-inverse-image-smooth-morphism, clause 4, proof Steps 9--10
(blueprint: lem-v8-smooth-tensor-composition-equation). -/
theorem smoothTensorCompositionEquation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (K : Etale.DerivedCategoryModule A Z) :
    (smoothDualizingCompMap A f g) ▷
        (Etale.upperStar (ModuleCat.{u + 1} A) (f ≫ g)).leftDerivedFunctor.obj K ≫
      Etale.dualizingComplexTensorMap A (f ≫ g) K ≫
        (smoothExceptionalCompIso A f g).hom.app K =
      (α_ (Etale.dualizingComplex A f)
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex A g))
        ((Etale.upperStar (ModuleCat.{u + 1} A) (f ≫ g)).leftDerivedFunctor.obj K)).hom ≫
      (Etale.dualizingComplex A f) ◁
        (((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex A g)) ◁
            (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K ≫
          (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
            (Etale.dualizingComplex A g)
            ((Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)).inv ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
            (Etale.dualizingComplexTensorMap A g K)) ≫
      Etale.dualizingComplexTensorMap A f
        ((Etale.rightDerivedUpperShriek A g).obj K)  := by
  set_option maxRecDepth 2000 in
    exact unitCompositionEtale A f g
      (smoothCompactSupportCompIso A f g) (smoothProjectionCompCompatible A f g)
      (Etale.projectionMapAssociativity A f) K

end

end AlgebraicGeometry.ProEtale
