/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverCoefficient

/-! # The over-W transition as a single mapped coefficient composite

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical transition maps.
(blueprint: sbc-lem-higher-image-over-map-coefficient).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] lowerStarPlusTransition

private theorem mapped_coefficient_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (H : D ⥤ E) {X : D} {Y Z T : C}
    (l : X ⟶ R.obj Y) (s : Y ⟶ Z) (c : Z ⟶ T) :
    H.map l ≫ H.map (R.map (s ≫ c)) = H.map (l ≫ R.map s) ≫ H.map (R.map c) := by
  rw [R.map_comp, H.map_comp, H.map_comp, Category.assoc]

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

private meta def coefficientStructuralExact
    (proof : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
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


/-- Functoriality expands the mapped composite into the two mapped factors.
Source: Tags 03Q8 and 09Z1. (blueprint: sbc-lem-higher-image-over-map-coefficient-factorization). -/
theorem higherDirectImageOverMap_coefficient_factorization
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) :
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
      (lowerStarPlusTransition Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w])
        (higherDirectImageRawOverComplex Λ G B) ≫
        R+((A.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
          (higherDirectImageRawOverCoefficient Λ G f)) =
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
      (lowerStarPlusTransition Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w])
        (higherDirectImageRawOverComplex Λ G B)) ≫
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
        (R+((A.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
        (higherDirectImageRawOverCoefficient Λ G f)) := by
  exact Functor.map_comp _ _ _

/-- Endpoint coherence identifies the factorized morphism with the canonical over-map.
Source: Tags 03Q8 and 09Z1. (blueprint: sbc-lem-higher-image-over-map-coefficient-endpoint). -/
theorem higherDirectImageOverMap_coefficient_endpoint
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) :
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
      (lowerStarPlusTransition Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w])
        (higherDirectImageRawOverComplex Λ G B)) ≫
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
        (R+((A.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
          (higherDirectImageRawOverCoefficient Λ G f)) =
      higherDirectImageOverMap Λ k G q f := by
  let K : DerivedCategory.Plus (Sheaf B.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (DerivedCategory.Plus.singleFunctor _ 0).obj (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
  let l := lowerStarPlusTransition Λ f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) K
  let s := (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
    (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
  let c := (DerivedCategory.Plus.singleFunctor _ 0).map
    ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
      (Over.w f).symm).inv.app G)
  let R := R+((A.hom ≫ k)_*[ModuleCat.{u + 1} Λ])
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let mut inputs := #[]
      for name in [`R, `H, `l, `s, `c] do
        inputs := inputs.push (← Lean.Meta.getLocalDeclFromUserName name).toExpr
      let proof ← Lean.Meta.mkAppM ``mapped_coefficient_comp inputs
      let proof ← Lean.Meta.zetaReduce proof
      coefficientStructuralExact proof

/-- Identify the homology map of the combined derived coefficient morphism with
 the canonical transition for coefficients restricted from W.
Source: Stacks Project, Tags 03Q8 and 09Z1, the canonical transition construction.
(blueprint: sbc-lem-higher-image-over-map-coefficient).

Proof: Let B₀=(B^*G)[0], A₀=(A^*G)[0], and M₀=(f^*B^*G)[0]. Write
s:f^*B₀→M₀ for the single-complex comparison and c:M₀→A₀ for the image under
the single functor of the inverse-image composition identification. Let R be the
derived direct image along A→S, H degree-q homology, and l the derived triangle
transition from the direct image of B₀ to R(f^*B₀). The left side is H(l ≫ R(s ≫ c)).
Functoriality of R gives R(s ≫ c)=R(s) ≫ R(c). Associativity gives
l ≫ R(s ≫ c)=(l ≫ R(s)) ≫ R(c). Functoriality of H gives
H(l ≫ R(s ≫ c))=H(l ≫ R(s)) ≫ H(R(c)). The first factor is exactly
higherDirectImageTransition by its definition; composing it with the second
factor is exactly higherDirectImageOverMap by its definition. This argument
is purely functorial and holds for every integer q, zero sheaves and identity
arrows, without geometric finiteness assumptions. No object is chosen. -/
theorem higherDirectImageOverMap_coefficient
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) :
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
      (lowerStarPlusTransition Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w])
        (higherDirectImageRawOverComplex Λ G B) ≫
        R+((A.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
          (higherDirectImageRawOverCoefficient Λ G f)) =
      higherDirectImageOverMap Λ k G q f := by
  exact (higherDirectImageOverMap_coefficient_factorization Λ k G q f).trans
    (higherDirectImageOverMap_coefficient_endpoint Λ k G q f)

end AlgebraicGeometry.Etale
