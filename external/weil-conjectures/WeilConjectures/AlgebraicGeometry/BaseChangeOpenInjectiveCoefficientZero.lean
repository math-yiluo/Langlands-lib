/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.LongExactSequence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.AlgebraicGeometry.EtaleOpenInjectiveLerayEdge
import WeilConjectures.AlgebraicGeometry.BaseChangeTargetCoefficientNaturality

/-! # Open injective coefficient comparison

Source: Stacks Project, Tag 0F07, closed–open part of the proof.
(blueprint: lem-sbc-open-injective-coefficient-zero)
-/

@[expose] public section

-- Construct this standard theorem application explicitly; Lean's kernel checks it.
private meta def toEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- The congruence method of HigherDirectImageRawTransitionToHomCore, which also reads through
-- `let`s and `(𝟭 _).obj`. Build congruence proofs before reducing the large derived-category
-- objects, so that the kernel only meets proof irrelevance at the leaves.
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
        | e' =>
          if (e'.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
              e'.isAppOfArity ``CategoryTheory.Functor.map 8) &&
              (e'.getArg! 4).isAppOfArity ``CategoryTheory.Functor.id 2 then
            e'.getAppArgs.back!
          else e'
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

-- Close the goal by `proof` along an explicit congruence proof between their types.
private meta def structuralExactProp (proof : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let target ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← goal.getType))
    let proofType ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← Lean.Meta.inferType proof))
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 200 proofType target)
    let h ← toEq h
    goal.assign (← Lean.Meta.mkAppM ``Eq.mp #[h, proof])

open Lean Elab Tactic in
/-- Close the goal by the given proof, along an explicit congruence proof between the types. -/
local elab "structural_exact " h:term : tactic => withMainContext do
  structuralExactProp (← elabTerm h none)

open Lean Meta Elab Tactic in
/-- Run the tactic block, then substitute all `let` values in the resulting proof term, so that
the kernel compares the expanded terms syntactically instead of unfolding through `let`s. -/
local elab "zeta_proof " t:tacticSeq : tactic => do
  let g ← getMainGoal
  g.withContext do
    let p ← mkFreshExprSyntheticOpaqueMVar (← g.getType)
    let gs ← Lean.Elab.Term.withSynthesize <| Lean.Elab.Tactic.run p.mvarId! (evalTactic t)
    unless gs.isEmpty do throwError "zeta_proof: unsolved goals"
    let pf ← instantiateMVars p
    let pf ← Meta.transform pf (post := fun e => match e with
      | .letE _ _ v b _ => return .visit (b.instantiate1 v)
      | _ => return .continue)
    let pf ← zetaReduce pf
    g.assign pf
    replaceMainGoal []

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private lemma eq_zero_of_comp_eq_zero {R : Type*} [Ring R] {M N P : ModuleCat R}
    {f : M ⟶ N} {g : N ⟶ P} (hg : Function.Injective g.hom) {z : M}
    (h : (f ≫ g).hom z = 0) : f.hom z = 0 :=
  hg (h.trans (map_zero g.hom).symm)

/-- The unit of an adjunction at `X`, with the source written as `X`. -/
private def unitApp {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (X : C) : X ⟶ R.obj (L.obj X) :=
  adj.unit.app X

/-- The counit of an adjunction at `Y`, with the target written as `Y`. -/
private def counitApp {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (Y : D) : L.obj (R.obj Y) ⟶ Y :=
  adj.counit.app Y

set_option backward.isDefEq.respectTransparency false in
private lemma adjoint_coefficient_cancel
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (F : C) (J : D) (α : L.obj F ⟶ J) :
    L.map (unitApp adj F ≫ R.map α) ≫ counitApp adj J = α := by
  have hc := adj.counit.naturality α
  simp only [Functor.comp_map, Functor.id_map] at hc
  rw [L.map_comp, Category.assoc]
  change L.map (adj.unit.app F) ≫ L.map (R.map α) ≫ adj.counit.app J = α
  rw [hc, ← Category.assoc]
  exact (congrArg (fun k ↦ k ≫ α) (adj.left_triangle_components F)).trans
    (Category.id_comp α)

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)

/-- A class that is a base-change image on V maps to zero after the open injective
coefficient embedding. This is the Leray part of the closed–open argument.

Source: Stacks Project, Tag 0F07, open summand in condition (3).
(blueprint: lem-sbc-open-injective-coefficient-zero)

Proof: put J = Injective.under (F restricted to V). The degree q source for J
vanishes since J is injective and q is positive. Naturality therefore sends the
assumed base-change image on V to zero in R^q(h composed with j')_* e_V^* J.
Apply the universal lower-degree hypothesis after the preliminary base change to T,
to the quasi-compact separated open immersion j:V -> T. In degree zero it identifies
e^* j_* J with j'_* e_V^* J. In degrees 1 through q-1 it implies that R^a j'_*
e_V^* J vanishes, since R^a j_* J vanishes by injectivity. The Leray edge map
R^q h_* e^* j_* J -> R^q(h composed with j')_* e_V^* J is consequently injective.
Compatibility of the edge map with the coefficient unit and target transition
identifies the image of the class under this injection with the zero just obtained.
Injectivity on stalks proves the asserted vanishing. The empty open causes no exception.
-/
theorem baseChange_open_injective_coefficient_eq_zero [IsAffine S]
    (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, UniversalBaseChangeProperty Λ p q')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    {T' : Scheme.{u}} (f : T' ⟶ T)
    [CompactSpace T'] [QuasiSeparatedSpace T']
    (ζ : baseChangeTargetStalk Λ p g q F x (Over.mk f))
    (V : T'.Opens) (hV : IsCompact (V : Set T'))
    (hζ : (baseChangeTargetStalkMap Λ p g q F x
      (Over.homMk V.ι : Over.mk (V.ι ≫ f) ⟶ Over.mk f)).hom ζ ∈
        Set.range (baseChangeStalkMap Λ p g q F x (Over.mk (V.ι ≫ f))).hom) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
      ((baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p)
        (pullback.snd (f ≫ g) p) q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.ι).unit.app
          (((f)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
            ((V.ι)_*[ModuleCat.{u + 1} Λ]).map
              (Injective.ι (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj
                (((f)^*[ModuleCat.{u + 1} Λ]).obj F)))))).hom ζ = 0 := by
  -- Work with the objects and maps in the form used by `baseChangeTargetStalkMap`
  -- (`U.hom`, `φ.left`), and only match the stated form at the end by a congruence proof.
  zeta_proof
    have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
    let U := Over.mk f
    let W := Over.mk (V.ι ≫ f)
    let φ : W ⟶ U := Over.homMk V.ι
    let F' := ((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F
    let : IsOpenImmersion φ.left := inferInstanceAs (IsOpenImmersion V.ι)
    let J := Injective.under (((φ.left)^*[ModuleCat.{u + 1} Λ]).obj F')
    let β : ((φ.left)^*[ModuleCat.{u + 1} Λ]).obj F' ⟶ J := Injective.ι _
    let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) φ.left
    let G := ((φ.left)_*[ModuleCat.{u + 1} Λ]).obj J
    let η := unitApp adj F' ≫ ((φ.left)_*[ModuleCat.{u + 1} Λ]).map β
    let e := pullback.fst (U.hom ≫ g) p
    let h := pullback.snd (U.hom ≫ g) p
    let eV := pullback.fst (W.hom ≫ g) p
    let hYV := pullback.snd (W.hom ≫ g) p
    let a : pullback (W.hom ≫ g) p ⟶ pullback (U.hom ≫ g) p :=
      pullback.lift (eV ≫ φ.left) hYV (by
        rw [Category.assoc, ← Category.assoc φ.left, Over.w]
        exact pullback.condition)
    have wa : a ≫ e = eV ≫ φ.left := pullback.lift_fst _ _ _
    have wh : a ≫ h = hYV := pullback.lift_snd _ _ _
    let B := baseChangeTargetFunctor Λ e h q
    let BV := baseChangeTargetFunctor Λ eV hYV q
    let fiber := (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
    let : fiber.Additive := (X.uliftPointSmallEtale x).sheafFiber_additive
    let : PreservesFiniteLimits fiber :=
      inferInstanceAs (PreservesFiniteLimits
        ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)))
    let t (K : Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      baseChangeTargetTransition Λ e h q φ.left a eV hYV wa wh K
    let E := t G ≫ BV.map (counitApp adj J)
    have hmono : Mono E := by
      let : CompactSpace V := isCompact_iff_compactSpace.mp hV
      let : QuasiCompact φ.left := inferInstanceAs (QuasiCompact V.ι)
      let : QuasiSeparated φ.left := inferInstanceAs (QuasiSeparated V.ι)
      have outer : IsPullback (a ≫ h) eV p (φ.left ≫ (U.hom ≫ g)) := by
        rw [wh, ← Category.assoc, Over.w φ]
        exact (IsPullback.of_hasPullback (W.hom ≫ g) p).flip
      have hs : IsPullback eV a φ.left e :=
        (outer.of_right wa (IsPullback.of_hasPullback (U.hom ≫ g) p).flip).flip
      have hm := baseChangeTargetTransition_counit_mono Λ h e φ.left eV a hYV wa wh hs q hq
        (fun n hn ↦ hprev n hn (U.hom ≫ g) h e
          (IsPullback.of_hasPullback (U.hom ≫ g) p).flip) J
      structural_exact hm
    let : Mono E := hmono
    have hi : Function.Injective (fiber.map E).hom :=
      (ModuleCat.mono_iff_injective _).mp (by infer_instance)
    let c := upperStarComp (ModuleCat.{u + 1} Λ) φ.left U.hom W.hom (Over.w φ).symm
    let γ : ((W.hom)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ J := c.hom.app F ≫ β
    have hβ := adjoint_coefficient_cancel adj F' J β
    have hc : c.inv.app F ≫ γ = β := by
      rw [← Category.assoc, Iso.inv_hom_id_app]
      exact Category.id_comp β
    have hn : B.map η ≫ E = t F' ≫ BV.map β := by
      have hn' := target_transition_naturality Λ e h q φ.left a eV hYV wa wh η
      rw [← Category.assoc, hn', Category.assoc, ← BV.map_comp, hβ]
    let y := Classical.choose hζ
    have hy := Classical.choose_spec hζ
    have hz :
        (fiber.map (BV.map γ)).hom ((baseChangeTargetStalkMap Λ p g q F x φ).hom ζ) = 0 := by
      rw [← hy]
      have hzero := baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ
        (IsPullback.of_hasPullback (W.hom ≫ g) p) (q := q) (by lia) γ
      have hfzero := congrArg fiber.map hzero
      rw [fiber.map_comp, fiber.map_zero] at hfzero
      exact congrArg (fun k ↦ k.hom y) hfzero
    have hsmap : baseChangeTargetStalkMap Λ p g q F x φ =
        fiber.map (t F' ≫ BV.map (c.inv.app F)) := rfl
    have hsquare : fiber.map (B.map η) ≫ fiber.map E =
        baseChangeTargetStalkMap Λ p g q F x φ ≫ fiber.map (BV.map γ) := by
      rw [hsmap, ← fiber.map_comp, ← fiber.map_comp, hn]
      congr 1
      calc
        t F' ≫ BV.map β = t F' ≫ BV.map (c.inv.app F ≫ γ) :=
          congrArg (fun k ↦ t F' ≫ BV.map k) hc.symm
        _ = (t F' ≫ BV.map (c.inv.app F)) ≫ BV.map γ := by
          rw [BV.map_comp]
          exact (Category.assoc _ _ _).symm
    have h' : (fiber.map (B.map η) ≫ fiber.map E).hom ζ = 0 := by
      rw [hsquare]
      exact hz
    have hfinal : (fiber.map (B.map η)).hom ζ = 0 := eq_zero_of_comp_eq_zero hi h'
    structural_exact hfinal

end AlgebraicGeometry.Etale
