/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.CompatiblePullbackSheafSystem
import WeilConjectures.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Mathlib.CategoryTheory.Presentable.Directed

/-! # Descent of fixed-base étale cohomology classes

Source: Stacks Project, Tag 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

-- Kernel-checked congruence, adapted from HigherDirectImageTransitionIsIsoOfLower.
-- Normalize local diagram aliases before comparing derived-cohomology objects.
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
      if a == b then return ← Lean.Meta.mkHEqRefl a
      if a.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl a).value? then
          return ← congrProofs cache pairs n value b
      if b.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl b).value? then
          return ← congrProofs cache pairs n a value
      if a.getAppFn.isFVar && !a.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl a.getAppFn).value? then
          return ← congrProofs cache pairs n (Lean.mkAppN value a.getAppArgs).headBeta b
      if b.getAppFn.isFVar && !b.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl b.getAppFn).value? then
          return ← congrProofs cache pairs n a (Lean.mkAppN value b.getAppArgs).headBeta
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
      if a.isAppOfArity ``Eq.mpr 4 then
        let args := a.getAppArgs
        let hs ← Lean.Meta.mkAppM ``Eq.symm #[args[2]!]
        let hc ← Lean.Meta.mkAppM ``cast_heq #[hs, args[3]!]
        let ht ← congrProofs cache pairs n args[3]! b
        return ← Lean.Meta.mkAppM ``HEq.trans #[hc, ht]
      if b.isAppOfArity ``Eq.mpr 4 then
        let args := b.getAppArgs
        let hs ← Lean.Meta.mkAppM ``Eq.symm #[args[2]!]
        let hc ← Lean.Meta.mkAppM ``cast_heq #[hs, args[3]!]
        let ht ← congrProofs cache pairs n a args[3]!
        let hc ← Lean.Meta.mkAppM ``HEq.symm #[hc]
        return ← Lean.Meta.mkAppM ``HEq.trans #[ht, hc]
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
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ==
            (← Lean.getConstInfo ``CategoryTheory.Functor.obj).type.getNumHeadForalls then
          let mut functor := args[args.size - 2]!
          for _ in [:20] do
            if functor.isFVar then
              if let some value := (← Lean.Meta.getFVarLocalDecl functor).value? then
                functor := value.headBeta
              else break
            else break
          let fs := functor.getAppArgs
          if functor.isAppOf ``CategoryTheory.Functor.obj && fs.size ==
              (← Lean.getConstInfo ``CategoryTheory.Functor.obj).type.getNumHeadForalls then
            if fs[fs.size - 2]!.isAppOf ``CategoryTheory.Functor.const then
              return fs.back!
          if functor.isAppOf ``CategoryTheory.Over.forget then
            return ← Lean.Meta.mkAppM ``CategoryTheory.Over.left #[args.back!]
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        if e.isAppOf ``CategoryTheory.Limits.Cone.pt && args.size ==
            (← Lean.getConstInfo ``CategoryTheory.Limits.Cone.pt).type.getNumHeadForalls then
          let cone := args.back!
          if cone.isAppOf ``CategoryTheory.Limits.Cone.whisker ||
              cone.isAppOf ``CategoryTheory.Functor.mapCone then
            return ← Lean.Meta.withTransparency .default (Lean.Meta.whnf e)
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
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
      let sameHead := af == bf || (af.isConst && bf.isConst &&
        af.constName! == bf.constName! && (← Lean.Meta.isDefEq af bf))
      if !sameHead || aa.size != ba.size then
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
        if ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq a b) then
          return ← Lean.Meta.mkHEqRefl a
        throwError "different heads: {a} versus {b}"
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
    let expected ← Lean.instantiateMVars (← goal.getType)
    let actual ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    if let some (_, lhs, rhs) := expected.eq? then
      if let some (_, lhs', rhs') := actual.eq? then
        let hl ← Lean.Meta.withTransparency .reducible
          (congrProofs cache #[] 300 lhs lhs')
        let hr ← Lean.Meta.withTransparency .reducible
          (congrProofs cache #[] 300 rhs' rhs)
        let hm ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
        let hh ← Lean.Meta.mkAppM ``HEq.trans #[hl, hm]
        let hh ← Lean.Meta.mkAppM ``HEq.trans #[hh, hr]
        goal.assign (← toEq hh)
        return
    let heq ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 200 expected actual)
    let eq ← toEq heq
    goal.assign (← Lean.Meta.mkAppM ``Eq.mpr #[eq, proof])

elab "continuity_structural_exact " n:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    structuralExact (← Lean.Meta.getLocalDeclFromUserName n.getId).toExpr

-- Close a conversion between definitionally equal types using the existing proof.
-- The kernel checks this assignment without elaborator unification.
elab "continuity_defeq_exact " n:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    goal.assign (← Lean.Meta.getLocalDeclFromUserName n.getId).toExpr

private theorem sheafH_iso_cancel
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {P Q : Sheaf J AddCommGrpCat.{u + 1}} (e : P ≅ Q) (q : ℕ)
    (x : Sheaf.H P q) (y : Sheaf.H Q q)
    (h : Sheaf.H.map (e.inv ≫ 𝟙 P) q y = x) : y = Sheaf.H.map e.hom q x := by
  rw [Category.comp_id] at h
  have hh := congrArg (Sheaf.H.map e.hom q) h
  simpa only [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply] using hh

attribute [local irreducible] upperStar cohomologyMap Sheaf.H.map
  CategoryTheory.Abelian.Ext.instAddCommGroup

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Every cohomology class of a sheaf pulled back from a fixed base descends to a stage.

Source: Stacks Project, Theorem 59.51.3, Tag 09YQ, and directed reindexing, Tag 0032.
(blueprint: lem-weil-pbc-fixed-base-cohomology-class-descent).

Proof:
1. Choose a nonempty small directed preorder and a final functor to I opposite.
   Its opposite is initial, so the reindexed underlying scheme cone is still limiting.
   Quasi-compactness, quasi-separatedness and affineness of transitions are inherited.
2. At each stage pull F back along its structure morphism to S. Use the inverse
   upperStarComp as transition. compatiblePullbackSheafSystem proves the identity,
   composition and cone compatibility equations. The corresponding diagram on the
   limit is constant with value the pullback of F along c.pt.hom.
3. The directed category is connected, so this constant sheaf cocone is colimiting.
   etale_limit_canonical_cohomology_diagram constructs the cohomology diagram and
   its cocone with the specified pullback-comparison legs. Apply
   nonempty_isColimit_etale_cohomology_of_isLimit to obtain its colimit property.
4. The forgetful functor from abelian groups preserves these filtered colimits.
   Hence every class is represented at a stage by Concrete.isColimit_exists_rep.
   The specified cocone leg identifies that representative's pullback, followed by
   H of the inverse composition comparison, with x. Apply H of the forward
   comparison and cancel the two isomorphisms. This is the displayed equation.

Edge cases: cofilteredness supplies a nonempty index; q = 0 needs no negative
cochains. Empty schemes and the zero sheaf give only the zero class. A constant
one-object diagram gives the usual inverse-image composition identification.
-/
theorem exists_cohomologyMap_preimage_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    ∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x := by
  classical
  intro x
  obtain ⟨J, hJ, hdir, hne, R, hR⟩ := IsFiltered.exists_directed Iᵒᵖ
  let E : Jᵒᵖ ⥤ Scheme.{u} :=
    { obj := fun j ↦ (D.obj (R.obj j.unop).unop).left
      map := fun f ↦ (D.map (R.map f.unop).unop).left
      map_id := fun j ↦ by
        change (D.map (R.map (𝟙 j.unop)).unop).left = _
        rw [R.map_id]
        change (D.map (𝟙 _)).left = _
        rw [D.map_id, Over.id_left]
      map_comp := fun f g ↦ by
        simp only [unop_comp, Functor.map_comp, Over.comp_left] }
  let : ∀ j : Jᵒᵖ, CompactSpace (E.obj j) :=
    fun j ↦ inferInstanceAs (CompactSpace (D.obj (R.obj j.unop).unop).left)
  let : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (E.obj j) :=
    fun j ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj (R.obj j.unop).unop).left)
  let : ∀ (j k : Jᵒᵖ) (f : j ⟶ k), IsAffineHom (E.map f) :=
    fun j k f ↦ inferInstanceAs (IsAffineHom (D.map (R.map f.unop).unop).left)
  let c₀ := (Over.forget S).mapCone c
  let d : Cone E :=
    { pt := c.pt.left
      π :=
        { app := fun j ↦ (c.π.app (R.obj j.unop).unop).left
          naturality := fun i j f ↦ by
            change 𝟙 _ ≫ (c.π.app (R.obj j.unop).unop).left =
              (c.π.app (R.obj i.unop).unop).left ≫ (D.map (R.map f.unop).unop).left
            rw [Category.id_comp, ← Over.comp_left, c.w] } }
  have hd' := (Functor.Initial.isLimitWhiskerEquiv R.leftOp c₀).symm hc
  have hd : IsLimit d := by continuity_defeq_exact hd'
  let v (j : J) : E.obj (op j) ⟶ S := (D.obj (R.obj j).unop).hom
  have wv (j k : J) (f : j ⟶ k) : v k = E.map f.op ≫ v j :=
    (Over.w (D.map (R.map f).unop)).symm
  have wt (j : J) : c.pt.hom = d.π.app (op j) ≫ v j :=
    (Over.w (c.π.app (R.obj j).unop)).symm
  let F' (j : J) :=
    (upperStar AddCommGrpCat.{u + 1} (D.obj (R.obj j).unop).hom).obj F
  let φ {j k : J} (f : j ⟶ k) :
      (upperStar AddCommGrpCat.{u + 1} (E.map f.op)).obj (F' j) ⟶ F' k :=
    (upperStarComp AddCommGrpCat.{u + 1} (E.map f.op) (v j) (v k) (wv j k f)).inv.app F
  let K := (upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F
  let G : J ⥤ Sheaf d.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    (Functor.const J).obj K
  let eG (j : J) : G.obj j ≅
      (upperStar AddCommGrpCat.{u + 1} (d.π.app (op j))).obj (F' j) :=
    (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (R.obj j).unop).left
      (D.obj (R.obj j).unop).hom c.pt.hom (Over.w (c.π.app (R.obj j).unop)).symm).app F
  have hs := compatiblePullbackSheafSystem E d S F v wv c.pt.hom wt
  have hidentity : ∀ i : J, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op i)))).hom.app
        (F' i) ≫ (upperStarId AddCommGrpCat.{u + 1} (E.obj (op i))).hom.app (F' i)  := by
    intro i
    have hh := hs.1 i
    continuity_structural_exact hh
  have hcomposition : ∀ (i j k : J) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (E.map g.op) (E.map f.op)
          (E.map (f ≫ g).op) (E.map_comp g.op f.op)).hom.app (F' i) ≫
        (upperStar AddCommGrpCat.{u + 1} (E.map g.op)).map (φ f) ≫ φ g  := by
    intro i j k f g
    have hh := hs.2.1 i j k f g
    continuity_structural_exact hh
  have hG : ∀ (i j : J) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op j)) (E.map f.op)
        (d.π.app (op i)) (d.w f.op).symm).hom.app (F' i) ≫
      (upperStar AddCommGrpCat.{u + 1} (d.π.app (op j))).map (φ f) ≫ (eG j).inv  := by
    intro i j f
    have hh := hs.2.2 i j f
    continuity_structural_exact hh
  obtain ⟨H, eH, hH, B, eB, hB⟩ := etale_limit_canonical_cohomology_diagram E d
    F' φ hidentity hcomposition G eG hG (constCocone J K) q
  let : IsConnected J := IsFiltered.isConnected J
  obtain ⟨hcolim⟩ := nonempty_isColimit_etale_cohomology_of_isLimit E d hd F' φ
    hidentity hcomposition G eG hG (constCocone J K) (isColimitConstCocone J K)
    q H eH hH B eB hB
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep H hcolim (eB.inv x)
  refine ⟨(R.obj j).unop, (eH j).hom y, ?_⟩
  have he := ConcreteCategory.congr_hom (hB j) y
  change eB.hom (B.ι.app j y) = Sheaf.H.map ((eG j).inv ≫ 𝟙 K) q
    (cohomologyMap (d.π.app (op j)) (F' j) q ((eH j).hom y)) at he
  have hx : Sheaf.H.map ((eG j).inv ≫ 𝟙 K) q
      (cohomologyMap (d.π.app (op j)) (F' j) q ((eH j).hom y)) = x :=
    he.symm.trans ((congrArg eB.hom hy).trans
      (ConcreteCategory.congr_hom eB.inv_hom_id x))
  have h := sheafH_iso_cancel c.pt.left.smallEtaleTopology (eG j) q x
    (cohomologyMap (d.π.app (op j)) (F' j) q ((eH j).hom y)) hx
  continuity_defeq_exact h

end AlgebraicGeometry.Etale
