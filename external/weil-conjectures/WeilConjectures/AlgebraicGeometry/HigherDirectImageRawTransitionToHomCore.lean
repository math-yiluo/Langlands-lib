/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback


public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct
import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionHomologyShift
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
private theorem map_factor
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {W X Y : C} {T Z Z' : D}
    (ε : T ⟶ H.obj W) (z : W ⟶ X) (z' : W ⟶ Y) (t : X ⟶ Y)
    (hz : z' = z ≫ t) (c : H.obj X ⟶ Z) (c' : H.obj Y ⟶ Z') (s : Z ⟶ Z')
    (hc : H.map t ≫ c' = c ≫ s) :
    ε ≫ H.map z' ≫ c' = (ε ≫ H.map z ≫ c) ≫ s := by
  rw [hz, H.map_comp]
  simp only [Category.assoc]
  rw [hc]

-- Construct this standard theorem application explicitly; Lean's kernel checks it.
private meta def toEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- Adapt the kernel-checked congruence method of HigherDirectImageTransitionCoreComposition.
-- Build congruence proofs before reducing the large derived-category objects.
private meta def congrProofs
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
        | e' => e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← congrProofs cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← congrProofs cache pairs n type type'
          let htype ← toEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← congrProofs cache (pairs.push (x, y, hxy)) n
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
        return ← congrProofs cache pairs n a' b'
      let af := a.getAppFn
      let bf := b.getAppFn
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
      if af != bf || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← congrProofs cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← congrProofs cache pairs n a b'
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
            return ← congrProofs cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← congrProofs cache pairs n a b'
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
        return ← congrProofs cache pairs n a' b'
      let mut first := 0
      while first < aa.size && aa[first]! == ba[first]! do
        first := first + 1
      let f := Lean.mkAppN af (aa.extract 0 first)
      let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
      let mut args := #[]
      for i in [first:aa.size] do
        let h ← congrProofs cache pairs n aa[i]! ba[i]!
        let h ← if ct.argKinds[i - first]! == .eq then
          toEq h else pure h
        args := args.push aa[i]! |>.push ba[i]! |>.push h
      return Lean.mkAppN ct.proof args
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

private meta def structuralExact (proof : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let target := (← Lean.Meta.whnf (← goal.getType)).consumeMData
    let some (_, lhs, rhs) := target.eq? | throwError "expected equality: {target}"
    let proofType ← Lean.Meta.whnf (← Lean.Meta.inferType proof)
    let some (_, lhs', rhs') := proofType.consumeMData.eq?
      | throwError "expected equality proof: {proofType}"
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let hl ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 200 lhs lhs')
    let hr ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 200 rhs' rhs)
    let hm ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
    let hh ← Lean.Meta.mkAppM ``HEq.trans #[hl, hm]
    let hh ← Lean.Meta.mkAppM ``HEq.trans #[hh, hr]
    goal.assign (← toEq hh)

set_option backward.isDefEq.respectTransparency true

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStarPlusComp upperStarComp
  Functor.mapDerivedCategoryPlusSingleFunctor lowerStarPlusTransition
  higherDirectImagePresheafToHom Adjunction.homEquiv Adjunction.derivedPlus
  derivedUpperStarLowerStarAdjunctionPlus

private theorem transitionThrough_eq
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus.transitionThrough
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)).derivedPlus
      D+((a)^*[ModuleCat.{u + 1} Λ])
      (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom K K' v =
    lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map v := by
  simp only [Adjunction.transitionThrough, lowerStarPlusTransition,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus, eqToIso_refl, Iso.refl_trans]
  erw [Functor.map_comp, Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
The morphism-level coherence underlying the raw pullback comparison.  It is obtained by
expanding the derived adjunction comparison, the transition map, and the shift comparison;
naturality of the adjunction unit and the triangle identity identify the two composites.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom-core).
-/
theorem higherDirectImageRawTransition_toHom_core
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale) :
    (higherDirectImagePresheafToHom Λ h' q K').app (op U) ∘
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) ≫
        (Functor.whiskerLeft (freeSheaf Λ S).op (preadditiveYoneda.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            (lowerStarPlusTransition Λ a h h' w K ≫
              R+((h')_*[ModuleCat.{u + 1} Λ]).map v)))).app (op U) := by
  set_option backward.isDefEq.respectTransparency true in
    subst h'
    ext z
    have hd := higherDirectImageRawTrianglePullback_adjunct Λ a h q K K' v U z
    rw [transitionThrough_eq] at hd
    have ht := higherDirectImageTransition_homologyShift Λ a h q K K' v
    have hf := map_factor
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0)
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
        ((freeSheaf Λ S).obj U)) _ _ _ hd _ _ _ ht
    have eh := higherDirectImagePresheafToHom_app_apply Λ h q K (op U) z
    have eh' := higherDirectImagePresheafToHom_app_apply Λ (a ≫ h) q K' (op U)
      (higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z)
    change (higherDirectImagePresheafToHom Λ (a ≫ h) q K').app (op U)
        (higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) z ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
          (lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫
            R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map v)
    rw [eh', eh]
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        structuralExact (← Lean.Meta.getLocalDeclFromUserName `hf).toExpr

end AlgebraicGeometry.Etale
