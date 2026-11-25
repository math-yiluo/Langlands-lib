/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
import Mathlib.Tactic

/-! # Extracting the normalized completed diagonal arrow

The finite and completed limit specification determines the normalized arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v₁ v₂ v₃ v₄ v₅ v₆ a b c w va vb vc r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalP1

private theorem selectNormalizedArrow
    {A : Sort v₁} {B : A → Sort v₂} {C : (a : A) → B a → Sort v₃}
    {D : (a : A) → (b : B a) → C a b → Sort v₄} {E : Sort v₅}
    {P : (a : A) → (b : B a) → (c : C a b) → D a b c → Prop}
    {Q : (a : A) → (b : B a) → (c : C a b) → D a b c → E → Prop}
    (h : ∃ a b c d, P a b c d)
    (select : ∀ a b c d, P a b c d → ∃ e, Q a b c d e) :
    ∃ e, ∃ a b c d, P a b c d ∧ Q a b c d e := by
  obtain ⟨a, b, c, d, h⟩ := h
  obtain ⟨e, he⟩ := select a b c d h
  exact ⟨e, a, b, c, d, h, he⟩

private theorem selectArrowEquation
    {A : Sort v₁} {P : A → Prop} {P₁ P₂ P₃ P₄ P₅ P₆ R : Prop}
    (h : P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ (∃! a, P a) ∧ R) : ∃ a, P a :=
  h.2.2.2.2.2.2.1.exists

-- Rearrange the dependent existence witnesses before specializing their large types.
private theorem selectLimitWitness
    {A : Sort v₁} {B : A → Sort v₂} {C : (a : A) → B a → Sort v₃}
    {D : (a : A) → (b : B a) → C a b → Sort v₄}
    {E : (a : A) → (b : B a) → (c : C a b) → D a b c → Sort v₅} {Z : Sort v₆}
    {P₁ P₂ P₃ R : (a : A) → (b : B a) → (c : C a b) →
      (d : D a b c) → E a b c d → Prop}
    {Q : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) →
      E a b c d → Z → Prop}
    (data : ∃ a b c d e, P₁ a b c d e ∧ P₂ a b c d e ∧ P₃ a b c d e ∧ R a b c d e)
    (select : ∀ a b c d e, R a b c d e → ∃ z, Q a b c d e z) :
    ∃ z a b c d e, P₁ a b c d e ∧ P₂ a b c d e ∧ P₃ a b c d e ∧ Q a b c d e z := by
  obtain ⟨a, b, c, d, e, h₁, h₂, h₃, h⟩ := data
  obtain ⟨z, hz⟩ := select a b c d e h
  exact ⟨z, a, b, c, d, e, h₁, h₂, h₃, hz⟩

private theorem normalizedLimit_exists
    (ℓ : ℕ) {A : Type a} [Category.{va} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    {C : Type c} [Category.{vc} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ C)] [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (L₀ : A ⥤ B) (D : DiagonalDerivedReduction ℓ L₀)
    (S U : A) (boundary : Ext S U 1)
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : C) (root : (ℕᵒᵖ ⥤ B) → Type r)
    (finite : ∀ H : ℕᵒᵖ ⥤ B, root H → Ext (D.ordinary.E.obj S) H 2 → Prop)
    (sourceNorm : (F.obj P ≅ limit (D.ordinary.E.obj S)) → Prop)
    (targetNorm : ∀ H : ℕᵒᵖ ⥤ B, root H → (F.obj Q ≅ limit H) → Prop)
    (data : DiagonalLimitDataSpec ℓ L₀ D S U boundary F P Q root finite sourceNorm targetNorm) :
    ∃ δ : (DerivedCategory.singleFunctor C 0).obj P ⟶
        ((DerivedCategory.singleFunctor C 0).obj Q) ⟦(2 : ℤ)⟧,
    ∃ (H : ℕᵒᵖ ⥤ B) (roots : root H)
      (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
        (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S))
      (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U) ⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor _ 0).obj H) ⟦(2 : ℤ)⟧)
      (cycle : Ext (D.ordinary.E.obj S) H 2),
      a.hom = diagonalDerivedSingleCounit ℓ L₀ D S ∧
      cycle.hom = a.inv ≫ D.T.map boundary.hom ≫ b.hom ∧ finite H roots cycle ∧
      ∃ (L : DiagonalRlim B) (M : DiagonalCompletedReductionData ℓ C)
        (s : F.obj P ≅ limit (D.ordinary.E.obj S)) (t : F.obj Q ≅ limit H),
        let G := F
        let R := G.mapDerivedCategory
        let source := diagonalSingleLimitComparison G L P _ _ s a
        let target := diagonalShiftedSingleLimitComparison G L Q _ _ t b
        (sourceNorm s ∧ targetNorm H roots t ∧
        DiagonalArrowCompatibility ℓ R L.R
          (fun n ↦ M.derived.T ⋙ ((evaluation ℕᵒᵖ C).obj (Opposite.op n)).mapDerivedCategory)
          (fun n ↦ ((evaluation ℕᵒᵖ B).obj (Opposite.op n)).mapDerivedCategory)
          M.unit L.projection ((DerivedCategory.singleFunctor _ 0).obj P)
          (((DerivedCategory.singleFunctor _ 0).obj Q) ⟦(2 : ℤ)⟧)
          (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S))
          (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj U) ⟦(1 : ℤ)⟧))
          (D.T.map boundary.hom) source target) ∧
        R.map δ ≫ target = source ≫ L.R.map (D.T.map boundary.hom) := by
  exact selectLimitWitness data (fun _ _ _ _ _ h ↦
    selectNormalizedArrow h (fun _ _ _ _ h ↦ selectArrowEquation h))

open Lean Meta Elab Tactic in
/-- Extract a completed diagonal arrow together with its full normalized limit
presentation from the simultaneous finite and completed limit specification. -/
theorem completedLimit_exists
    (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (data : DiagonalCompletedLimitSpec ℓ Y hY D) :
    ∃ δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y,
      DiagonalTrace.IsDiagonalLimit ℓ Y hY D δ := by
  -- Preserve the source proposition's cached instance proofs in the application.
  run_tac do
    let data := (← getLocalDeclFromUserName `data).toExpr
    let some source ← unfoldDefinition? (← inferType data) |
      throwError "Cannot unfold the completed-limit specification"
    unless source.isAppOf ``DiagonalLimitDataSpec do
      throwError "Unexpected completed-limit specification"
    let proof ← mkAppOptM ``normalizedLimit_exists
      ((source.getAppArgs.map some).push (some data))
    closeMainGoal `normalized_limit proof

end AlgebraicGeometry.ProEtale.RationalP1
