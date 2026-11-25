/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence

/-! Categorical assembly for the canonical ambient pullback comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1

-- Explicit nested sources keep composite-functor conversions small.
private theorem assemble_from_leg_equations
    {C D₁ D₂ E : Type*} [Category C] [Category D₁] [Category D₂] [Category E]
    {P₁ P₂ : C ⥤ E}
    (F₁ : C ⥤ D₁) (F₂ : D₁ ⥤ E) (G₁ : C ⥤ D₂) (G₂ : D₂ ⥤ E)
    (c₁ : P₁ ≅ F₁ ⋙ F₂) (c₂ : P₂ ≅ G₁ ⋙ G₂) (t : P₂ ≅ P₁)
    {A : C} {B : D₁} {B' : D₂} {Q : E}
    (e : F₁.obj A ⟶ B) (j : G₁.obj A ⟶ B')
    (d : F₂.obj B ⟶ Q) (e₂ : G₂.obj B' ⟶ Q)
    (s₁ : P₁.obj A ⟶ Q) (s₂ : P₂.obj A ⟶ Q)
    (h₁ : c₁.hom.app A ≫
      (show F₂.obj (F₁.obj A) ⟶ Q from F₂.map e ≫ d) = s₁)
    (h₂ : c₂.hom.app A ≫
      (show G₂.obj (G₁.obj A) ⟶ Q from G₂.map j ≫ e₂) = s₂)
    (he : t.hom.app A ≫ s₁ = s₂) :
    (c₂.symm ≪≫ t ≪≫ c₁).hom.app A ≫
      (show F₂.obj (F₁.obj A) ⟶ Q from F₂.map e ≫ d) =
      (show G₂.obj (G₁.obj A) ⟶ Q from G₂.map j ≫ e₂) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁, he, ← h₂, Iso.inv_hom_id_app_assoc]

/-- Ambient square assembly: expand the pullback comparison and cancel the
compositor. The two leg equations and commutativity of the square
reduce the result to associativity. -/
theorem ambient_square_assembly
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (QuotientChange.Modules Λ Y)}
    {B : DerivedCategory (QuotientChange.Modules Λ X)}
    {B' : DerivedCategory (QuotientChange.Modules Λ Y')}
    {Q : DerivedCategory (QuotientChange.Modules Λ X')}
    (e : (QuotientChange.L Λ f).obj A ⟶ B)
    (j : (QuotientChange.L Λ g).obj A ⟶ B')
    (d : (QuotientChange.L Λ g').obj B ⟶ Q)
    (e₂ : (QuotientChange.L Λ f').obj B' ⟶ Q)
    (s₁ : (QuotientChange.L Λ (g' ≫ f)).obj A ⟶ Q)
    (s₂ : (QuotientChange.L Λ (f' ≫ g)).obj A ⟶ Q)
    (h₁ : (QuotientChange.scalarPullbackComposition Λ g' f).hom.app A ≫
      (show (QuotientChange.L Λ g').obj
        ((QuotientChange.L Λ f).obj A) ⟶ Q from
          (QuotientChange.L Λ g').map e ≫ d) = s₁)
    (h₂ : (QuotientChange.scalarPullbackComposition Λ f' g).hom.app A ≫
      (show (QuotientChange.L Λ f').obj
        ((QuotientChange.L Λ g).obj A) ⟶ Q from
          (QuotientChange.L Λ f').map j ≫ e₂) = s₂)
    (he : (eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
      sq.toCommSq.w.symm)).hom.app A ≫ s₁ = s₂) :
    ((QuotientChange.scalarPullbackComposition Λ f' g).symm ≪≫
      eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
        sq.toCommSq.w.symm) ≪≫
      QuotientChange.scalarPullbackComposition Λ g' f).hom.app A ≫
      (show (QuotientChange.L Λ g').obj
        ((QuotientChange.L Λ f).obj A) ⟶ Q from
          (QuotientChange.L Λ g').map e ≫ d) =
      (show (QuotientChange.L Λ f').obj
        ((QuotientChange.L Λ g).obj A) ⟶ Q from
          (QuotientChange.L Λ f').map j ≫ e₂) := by
  exact assemble_from_leg_equations
    (QuotientChange.L Λ f) (QuotientChange.L Λ g')
    (QuotientChange.L Λ g) (QuotientChange.L Λ f')
    (QuotientChange.scalarPullbackComposition Λ g' f)
    (QuotientChange.scalarPullbackComposition Λ f' g)
    (eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
      sq.toCommSq.w.symm)) e j d e₂ s₁ s₂ h₁ h₂ he
end AlgebraicGeometry.ProEtale.RationalP1
