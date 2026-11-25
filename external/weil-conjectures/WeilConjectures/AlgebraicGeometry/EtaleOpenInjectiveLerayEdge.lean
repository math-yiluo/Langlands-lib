/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparison

/-! # Open injective Leray edge comparison

Source: Stacks Project, Tags 0F07 and 0734.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

private theorem mono_rightDerived_map_of_lower_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] {K L : DerivedCategory.Plus C} (α : K ⟶ L)
    (q : ℤ) (hq : 1 ≤ q) [K.IsLE 0]
    (hα : ∀ n < q, IsIso ((DerivedCategory.Plus.homologyFunctor C n).map α)) :
    Mono ((DerivedCategory.Plus.homologyFunctor D q).map (R+(F).map α)) := by
  obtain ⟨M, b, c, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α b c
  have hM : M.IsGE q := by
    apply (M.isGE_ι_obj_iff q).mp
    apply (DerivedCategory.isGE_iff _ q).mpr
    intro n hn
    have := hα n hn
    have hn1α : Mono ((DerivedCategory.Plus.homologyFunctor C (n + 1)).map α) := by
      by_cases h : n + 1 < q
      · have := hα (n + 1) h
        infer_instance
      · have hz := DerivedCategory.Plus.isZero_homology_of_isLE K 0 (n + 1) (by lia)
        exact hz.mono _
    exact ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_exact₃
      T hT n (n + 1) rfl).isZero_X₂
      (((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff
        T hT n).mp (by
          change Epi ((DerivedCategory.Plus.homologyFunctor C n).map α)
          infer_instance))
      (((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
        T hT n (n + 1) rfl).mp hn1α)
  have hRT := R+(F).map_distinguished T hT
  have hz := F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    M q (q := q - 1) (by lia)
  exact ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_mono_shift_map_mor₁_iff
    (R+(F).mapTriangle.obj T) hRT (q - 1) q (by lia)).mpr (hz.eq_of_src _ _)

/-- Monicity of a composite `H(t ≫ R'(s)) ≫ H(R'(t'))` from monicity of `H(R₂(u ≫ R₁(σ)))`,
once `t` factors through an isomorphism `R₁ ⋙ R₂ ≅ R'` and `σ = s ≫ t'`.
Stated over abstract categories, so that its kernel check never unfolds derived functors. -/
private theorem mono_map_comp_of_factor
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    (R₁ : C₂ ⥤ C₁) (R₂ : C₁ ⥤ C₃) (R' : C₂ ⥤ C₃) (H : C₃ ⥤ C₄) (c : R₁ ⋙ R₂ ≅ R')
    {K : C₁} {W₁ W₂ W₃ : C₂} {t : R₂.obj K ⟶ R'.obj W₁} {u : K ⟶ R₁.obj W₁}
    (ht : t = R₂.map u ≫ c.hom.app W₁) {σ : W₁ ⟶ W₃} {s : W₁ ⟶ W₂} {t' : W₂ ⟶ W₃}
    (hm : Mono (H.map (R₂.map (u ≫ R₁.map σ)))) (hσ : σ = s ≫ t') :
    Mono (H.map (t ≫ R'.map s) ≫ H.map (R'.map t')) := by
  subst ht hσ
  have hn := c.hom.naturality (s ≫ t')
  dsimp only [Functor.comp_map] at hn
  have : H.map ((R₂.map u ≫ c.hom.app W₁) ≫ R'.map s) ≫ H.map (R'.map t') =
      H.map (R₂.map (u ≫ R₁.map (s ≫ t'))) ≫ H.map (c.hom.app W₃) := by
    rw [← H.map_comp, ← H.map_comp, R₂.map_comp]
    simp only [Category.assoc]
    rw [hn, R'.map_comp]
  rw [this]
  infer_instance

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

universe u
namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem lower_transition_factor
    {X Y W : Scheme.{u}} (h : Y ⟶ X) (a : W ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let : (((a)_*[ModuleCat.{u + 1} Λ])).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
    lowerStarPlusTransition Λ a h (a ≫ h) rfl K =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app K) ≫
      (Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
        ((h)_*[ModuleCat.{u + 1} Λ])
        (lowerStarComp (ModuleCat.{u + 1} Λ) a h)).hom.app
          (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  let : (((a)_*[ModuleCat.{u + 1} Λ])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
  let adj := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus
  let adjA := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus
  let C := Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
    ((h)_*[ModuleCat.{u + 1} Λ]) (lowerStarComp (ModuleCat.{u + 1} Λ) a h)
  have hn := C.hom.naturality
    (D+((a)^*[ModuleCat.{u + 1} Λ]).map (adj.counit.app K))
  have hu := adjA.unit.naturality (adj.counit.app K)
  simp only [Functor.comp_map, Functor.id_map] at hn hu
  unfold lowerStarPlusTransition
  rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    eqToIso_refl, Iso.refl_trans, Functor.map_comp, ← Category.assoc]
  rw [show upperStarPlusComp (ModuleCat.{u + 1} Λ) a h =
      upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h from rfl]
  rw [derivedPlus_unit_comp_upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h]
  change (adj.unit.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
    R+((h)_*[ModuleCat.{u + 1} Λ]).map
      (adjA.unit.app (D+((h)^*[ModuleCat.{u + 1} Λ]).obj
        (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) ≫
        C.hom.app (D+((a)^*[ModuleCat.{u + 1} Λ]).obj
          (D+((h)^*[ModuleCat.{u + 1} Λ]).obj
            (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)))) ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        (D+((a)^*[ModuleCat.{u + 1} Λ]).map (adj.counit.app K)) =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map (adjA.unit.app K) ≫ C.hom.app _
  simp only [Category.assoc]
  erw [← hn]
  rw [← Functor.map_comp_assoc]
  erw [← hu]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, adj.right_triangle_components]
  exact Category.id_comp _

/-- The open coefficient counit induces a monic degree-q Leray edge map.
Source: Stacks Project, Tags 0F07 and 0734.
(blueprint: lem-sbc-open-injective-leray-edge).

Proof: Let K = e^*((j_*J)[0]) and let α be the derived unit for a followed by
the pullback comparison and the single of the coefficient counit. The lower-degree
comparison identifies H^n(α) with base change for n < q, so these maps are isomorphisms.
K is concentrated in degree zero. The long exact sequence of its cone triangle gives
H^n(cone α) = 0 for n < q: use the isomorphism in degree n, and either the isomorphism
in degree n+1 or the vanishing of H^(n+1)(K) when n+1 ≥ q. Derived h_* preserves this
lower bound. Its long exact sequence therefore makes H^q(Rh_*(α)) monic.
The composition law for the derived adjunction units identifies the displayed transition
and coefficient counit with this map followed by the derived pushforward composition
isomorphism. Taking homology preserves that isomorphism and hence monicity.
-/
theorem baseChangeTargetTransition_counit_mono
    {X Y T V W : Scheme.{u}} (h : Y ⟶ X) (e : Y ⟶ T) (j : V ⟶ T)
    (eV : W ⟶ V) (a : W ⟶ Y) (h' : W ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (wa : a ≫ e = eV ≫ j) (wh : a ≫ h = h')
    (sq : IsPullback eV a j e) (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ n < q, BaseChangeProperty Λ e n)
    (J : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    Mono (baseChangeTargetTransition Λ e h q j a eV h' wa wh
      (((j)_*[ModuleCat.{u + 1} Λ]).obj J) ≫
      (baseChangeTargetFunctor Λ eV h' q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J)) := by
  subst h'
  let : (((a)_*[ModuleCat.{u + 1} Λ])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
  let K := D+((e)^*[ModuleCat.{u + 1} Λ]).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (((j)_*[ModuleCat.{u + 1} Λ]).obj J))
  have hK : K.IsLE 0 := by
    exact Functor.IsTExact.isLE_obj DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t D+((e)^*[ModuleCat.{u + 1} Λ]) _ 0
  let : ((𝟭 _).obj K).IsLE 0 := hK
  have hm := mono_rightDerived_map_of_lower_isIso ((h)_*[ModuleCat.{u + 1} Λ])
    _ q hq (fun n hn ↦ open_injective_coefficient_lower_comparison Λ e j eV a
      wa sq n (hprev n hn) J)
  -- Assemble the composite from the statements of the lemmas, then match it with the goal
  -- by an explicit congruence proof rather than by kernel unfolding.
  have hE := mono_map_comp_of_factor _ _ _ (DerivedCategory.Plus.homologyFunctor _ q)
    (Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
      ((h)_*[ModuleCat.{u + 1} Λ]) (lowerStarComp (ModuleCat.{u + 1} Λ) a h))
    (lower_transition_factor Λ h a K) hm
    (s := (upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
          eqToHom (by rw [wa]) ≫
          (upperStarPlusComp (ModuleCat.{u + 1} Λ) eV j).hom.app _ ≫
          D+((eV)^*[ModuleCat.{u + 1} Λ]).map
            ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              (((j)_*[ModuleCat.{u + 1} Λ]).obj J)))
    (t' := D+((eV)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J)))
    (by simp only [Functor.map_comp, Category.assoc])
  unfold baseChangeTargetTransition baseChangeTargetFunctor
  dsimp only [Functor.comp_map, Functor.comp_obj]
  structural_exact hE

end AlgebraicGeometry.Etale
