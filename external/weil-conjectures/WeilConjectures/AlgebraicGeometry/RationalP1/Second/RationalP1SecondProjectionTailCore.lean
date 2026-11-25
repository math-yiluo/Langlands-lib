/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionInterchangeCore
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ExtractionProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeSecondExtractProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparisonExpansion
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TensorShiftNaturality
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ShiftedTateSelfBraiding
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1StrengthProjectionAction

/-! # Cancellation of the fixed projection tail -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

private theorem comparison_tail
    {C : Type*} [Category C] [MonoidalCategory C]
    (J : C ⥤ C) (T : C) {U V D M : C}
    (sU : U ⊗ T ≅ J.obj U) (sV : V ⊗ T ≅ J.obj V)
    (sUT : (U ⊗ T) ⊗ T ≅ J.obj (U ⊗ T)) (sD : D ⊗ T ≅ J.obj D)
    (a : D ≅ J.obj V) (d : M ≅ J.obj U) (b : U ≅ V)
    (β : T ⊗ T ⟶ T ⊗ T) (hb : β = 𝟙 (T ⊗ T))
    (x : U ⊗ T ⟶ D) (hx : x = tensorHom b.hom (𝟙 T) ≫ sV.hom ≫ a.inv)
    (hnx : sUT.hom ≫ J.map x = tensorHom x (𝟙 T) ≫ sD.hom)
    (hnb : tensorHom b.hom (𝟙 T) ≫ sV.hom = sU.hom ≫ J.map b.hom) :
    (d.hom ▷ T) ≫ (sU.inv ▷ T) ≫ (α_ U T T).hom ≫
        (U ◁ β) ≫ (α_ U T T).inv ≫ sUT.hom ≫ J.map x =
      ((d.hom ≫ J.map b.hom ≫ a.inv) ▷ T) ≫ sD.hom := by
  simp only [tensorHom_id] at hx hnx hnb
  rw [hb]
  simp only [whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_assoc]
  rw [hnx]
  have ht : d.hom ≫ sU.inv ≫ x = d.hom ≫ J.map b.hom ≫ a.inv := by
    rw [hx, reassoc_of% hnb, Iso.inv_hom_id_assoc]
  simpa only [comp_whiskerRight, Category.assoc] using
    congrArg (fun f : M ⟶ D ↦ (f ▷ T) ≫ sD.hom) ht

private theorem inverse_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : D ⥤ E) {F G : C ⥤ D} (e : F ≅ G) (K : C)
    {U V : E} (a : U ≅ J.obj (G.obj K)) (d : V ≅ J.obj (F.obj K)) :
    d.hom ≫ J.map (e.hom.app K) ≫ a.inv =
      (a ≪≫ J.mapIso (e.symm.app K) ≪≫ d.symm).inv := by
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Iso.app_inv, Category.assoc]

-- Build the definitional comparison by cached heterogeneous congruence.
-- Each step is an ordinary equality proof checked by the kernel. Keeping repeated
-- instance comparisons shared avoids unfolding the native tensor constructions.
open Lean Meta Elab Tactic in
private meta def expandProjection (e : Expr) : MetaM Expr := do
  let .proj n i receiver := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) n | return e
  let field := n ++ info.fieldNames[i]!
  return mkAppN (← mkAppM field #[receiver]) e.getAppArgs

open Lean Meta Elab Tactic in
private meta partial def structuralRefl (g : MVarId) (fuel : Nat) :
    StateRefT (ExprMap Expr) MetaM Unit :=
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    if let some proof := (← get).get? target then
      g.assign proof
      return
    let h ← mkFreshExprSyntheticOpaqueMVar target
    structuralReflCore h.mvarId! fuel
    let proof ← instantiateMVars h
    if proof.hasMVar then throwError "incomplete structural congruence"
    modify fun cache => cache.insert target proof
    g.assign proof
where
  structuralReflCore (g : MVarId) (fuel : Nat) :
      StateRefT (ExprMap Expr) MetaM Unit := g.withContext do
    if fuel == 0 then throwError "structural reflexivity exhausted"
    let target ← g.getType
    let (lhs, rhs) ←
      if let some (_, lhs, rhs) := target.eq? then pure (lhs, rhs)
      else if let some (_, lhs, _, rhs) := target.heq? then pure (lhs, rhs)
      else throwError "expected equality"
    if lhs == rhs then
      if target.isHEq then g.assign (← mkHEqRefl lhs)
      else g.assign (← mkEqRefl lhs)
    else if (← isProof lhs) && (← isProof rhs) then
      let proof ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      let proof ← if target.isHEq then pure proof else mkEqOfHEq proof
      g.assign proof
    else if lhs.isLambda && rhs.isLambda then
      let ge ← g.heqOfEq
      let gs ← ge.apply (← mkConstWithFreshMVarLevels ``funext)
      for h in gs do
        let (_, h) ← h.intro1
        structuralRefl h (fuel - 1)
    else if lhs.isApp && lhs.getAppFn == rhs.getAppFn then
      let gh ← g.eqOfHEq
      let ct ← mkHCongrWithArity lhs.getAppFn lhs.getAppNumArgs
      let cp ← abstractProof ct.proof
      let gs ← gh.apply cp { synthAssignedInstances := false }
      for h in gs do structuralRefl h (fuel - 1)
    else
      let lhs' ← expandProjection lhs
      let rhs' ← expandProjection rhs
      let lhs' ← if lhs' == lhs then withTransparency .all (whnf lhs) else pure lhs'
      let rhs' ← if rhs' == rhs then withTransparency .all (whnf rhs) else pure rhs'
      if lhs' == lhs && rhs' == rhs then
        g.refl
      else
        let ty ← if target.isHEq then mkHEq lhs' rhs' else mkEq lhs' rhs'
        let h ← mkFreshExprSyntheticOpaqueMVar ty
        g.assign h
        structuralRefl h.mvarId! (fuel - 1)

open Lean Meta Elab Tactic in
local elab "structural_rfl" : tactic => do
  let _ ← (structuralRefl (← getMainGoal) 100).run {}
  replaceMainGoal []

/-- The fixed extraction composite agrees with the native generic construction. -/
private theorem second_extract_native
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    secondExtractProjection l c k p hpl Y K =
      nativeSecondExtractProjection (coefficient l c).X Y
        (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
        (firstLineComparisonForTrace l c k p hpl Y) K := by
  structural_rfl

/-- The two generic constructions of the extraction composite agree. -/
private theorem native_extract_generic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (LS : Modules Λ (ProjectiveLine Y)) (LX : Modules Λ (diagonalSurface Y))
    (e : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS)
        ⟦(2 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LX)
        ⟦(2 : ℤ)⟧))
    (K : DerivedCategory (Modules Λ Y)) :
    nativeSecondExtractProjection Λ Y LS LX e K =
      extractionProjectionMap Λ (secondProjection Y) (firstProjection Y) LS LX e
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)
        ((ambientPullbackComparison Λ (square Y)).app K) := by
  delta extractionProjectionMap extractionInsideMap nativeSecondExtractProjection
  rfl

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap shiftedLineComparison
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- Fixed tail cancellation with the unused local bindings eliminated.
The projection/strength action reduces the tail to its inside tensor maps.
Even Tate self-braiding and tensor-shift naturality cancel these maps, and the
canonical square comparison identifies the remaining inverse pull comparison. -/
theorem second_projection_tail_cancellation_expanded
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    let Λ := (coefficient l c).X
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let H := twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
    let Q := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    let T := (((DerivedCategory.singleFunctor
      (Modules Λ (diagonalSurface Y)) 0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    secondTraceStrengthTail Λ Y (line l c (ProjectiveLine Y)) K Q ≫
        H.map (secondExtractProjection l c k p hpl Y K) ≫
        twistProjectionMap Λ (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K))) =
      (projectionMap Λ (secondProjection Y))
        (H.obj (F.obj K)) T ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (tensorHom (secondPullComparison l c k p hpl Y K).inv (𝟙 T) ≫
            (tensorShiftIso Λ (diagonalSurface Y) (line l c (diagonalSurface Y))
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
            (H.obj (F.obj K)))).hom) := by
  let Λ := (coefficient l c).X
  let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  let P := moduleObjectDerivedPullback Λ (secondProjection Y)
  let P₁ := moduleObjectDerivedPullback Λ (firstProjection Y)
  let R := moduleObjectDerivedPushforward Λ (secondProjection Y)
  let LS := line l c (ProjectiveLine Y)
  let LX := line l c (diagonalSurface Y)
  let H := twist Λ (ProjectiveLine Y) LS
  let J := twist Λ (diagonalSurface Y) LX
  let T := (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LX)
    ⟦(2 : ℤ)⟧)
  let D := P₁.obj (H.obj A)
  let e₁ := firstLineComparisonForTrace l c k p hpl Y
  let e₂ := secondLineComparison l c k p hpl Y
  let a := pullTwistIso Λ (firstProjection Y) LS LX e₁ A
  let d := pullTwistIso Λ (secondProjection Y) LS LX e₂ A
  let b := (ambientPullbackComparison Λ (square Y)).app K
  let x := extractionInsideMap Λ (secondProjection Y) (firstProjection Y) LS LX e₁ A b
  let : ∀ z : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField z) :=
    fun z ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) z).invertible
  let : ∀ z : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField z) :=
    fun z ↦ (residueIsUnit l k p hpl _
      (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) z).invertible
  let a' := pullTwistIso Λ (firstProjection Y) LS LX
    (shiftedLineComparison l c (firstProjection Y)) A
  have hea : e₁ = shiftedLineComparison l c (firstProjection Y) := by
    unfold e₁ firstLineComparisonForTrace
    rfl
  have ha : a = a' := congrArg
    (fun e ↦ pullTwistIso Λ (firstProjection Y) LS LX e A) hea
  have hc : d.hom ≫ J.map b.hom ≫ a.inv =
      (secondPullComparison l c k p hpl Y K).inv := by
    have h₁ := congrArg
      (fun aa : D ≅ J.obj (P₁.obj A) ↦ d.hom ≫ J.map b.hom ≫ aa.inv) ha
    have h₂ := inverse_comparison J (ambientPullbackComparison Λ (square Y)) K a' d
    have h₃ := second_pull_comparison_inv_expansion l c k p hpl Y K
    exact h₁.trans (h₂.trans h₃.symm)
  have hb : (tensorBraiding Λ (diagonalSurface Y) T T).hom = 𝟙 (T ⊗ T) :=
    shifted_tate_self_braiding l c (diagonalSurface Y)
  have hi := comparison_tail J T
    (tensorShiftIso Λ (diagonalSurface Y) LX (P.obj A))
    (tensorShiftIso Λ (diagonalSurface Y) LX (P₁.obj A))
    (tensorShiftIso Λ (diagonalSurface Y) LX (P.obj A ⊗ T))
    (tensorShiftIso Λ (diagonalSurface Y) LX D) a d b
    (tensorBraiding Λ (diagonalSurface Y) T T).hom hb x
    (extractionInsideMap_eq Λ (secondProjection Y) (firstProjection Y) LS LX e₁ A b)
    (tensorShiftIso_naturality Λ (diagonalSurface Y) LX x).symm
    (tensorShiftIso_naturality Λ (diagonalSurface Y) LX
      (A := P.obj A) (B := P₁.obj A) b.hom)
  have he := congrArg
    (fun f : P.obj (H.obj A) ⟶ D ↦
      (f ▷ T) ≫ (tensorShiftIso Λ (diagonalSurface Y) LX D).hom) hc
  have hi := hi.trans he
  have hp := second_trace_strength_projection_action Λ Y (diagonalSurface Y)
    (secondProjection Y) LS LX e₂ K T D x
  have hir := congrArg
    (fun f : P.obj (H.obj A) ⊗ T ⟶ J.obj D ↦
      projectionMap Λ (secondProjection Y) (H.obj A) T ≫ R.map f) hi
  have hp := hp.trans hir
  have hex : secondExtractProjection l c k p hpl Y K =
      projectionMap Λ (secondProjection Y) A T ≫ R.map x := by
    exact ((second_extract_native l c k p hpl Y K).trans
      (native_extract_generic Λ Y LS LX e₁ K)).trans
      (extractionProjectionMap_eq Λ (secondProjection Y) (firstProjection Y) LS LX e₁ A b)
  have hl := congrArg
    (fun f : A ⊗ R.obj T ⟶ R.obj D ↦
      secondTraceStrengthTail Λ Y LS K (R.obj T) ≫ H.map f ≫
        twistProjectionMap Λ (secondProjection Y) LS LX e₂ D) hex
  have hr := congrArg
    (fun f : P.obj (H.obj A) ⊗ T ⟶ D ⊗ T ↦
      projectionMap Λ (secondProjection Y) (H.obj A) T ≫ R.map
        (f ≫ (tensorShiftIso Λ (diagonalSurface Y) LX D).hom))
    (tensorHom_id (secondPullComparison l c k p hpl Y K).inv T)
  exact hl.trans (hp.trans hr.symm)

end AlgebraicGeometry.ProEtale.RationalP1
