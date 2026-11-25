/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! Transition-compatible comparisons assembled from finite-stage inclusion cones. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace CategoryTheory.StageSystem

private def comparison_at_stage
    {A₀ B₀ C₀ A B C : Type*}
    [Category A₀] [Category B₀] [Category C₀] [Category A] [Category B] [Category C]
    (Ai : A₀ ⥤ B₀) (Bi : A₀ ⥤ C₀) (Pi : C₀ ⥤ B₀)
    (IX : A₀ ⥤ A) (IY : B₀ ⥤ B) (IZ : C₀ ⥤ C)
    (F : A ⥤ B) (G : A ⥤ C) (H : C ⥤ B)
    (a : Ai ⋙ IY ≅ IX ⋙ F) (b : Bi ⋙ IZ ≅ IX ⋙ G)
    (p : Pi ⋙ IY ≅ IZ ⋙ H) (r : Ai ≅ Bi ⋙ Pi) : IX ⋙ F ≅ IX ⋙ (G ⋙ H) :=
  a.symm ≪≫ Functor.isoWhiskerRight r IY ≪≫ Functor.associator Bi Pi IY ≪≫
    Functor.isoWhiskerLeft Bi p ≪≫ (Functor.associator Bi IZ H).symm ≪≫
    Functor.isoWhiskerRight b H ≪≫ Functor.associator IX G H

attribute [local irreducible] comparison_at_stage

private theorem paste_target_comparison
    {A₀ A₁ B₀ B₁ C₀ C₁ A B C : Type*}
    [Category A₀] [Category A₁] [Category B₀] [Category B₁]
    [Category C₀] [Category C₁] [Category A] [Category B] [Category C]
    (TX : A₀ ⥤ A₁) (TY : B₀ ⥤ B₁) (TZ : C₀ ⥤ C₁)
    (IX₀ : A₀ ⥤ A) (IX₁ : A₁ ⥤ A)
    (IY₀ : B₀ ⥤ B) (IY₁ : B₁ ⥤ B)
    (IZ₀ : C₀ ⥤ C) (IZ₁ : C₁ ⥤ C)
    (tX : TX ⋙ IX₁ ≅ IX₀) (tY : TY ⋙ IY₁ ≅ IY₀) (tZ : TZ ⋙ IZ₁ ≅ IZ₀)
    (A₀F : A₀ ⥤ B₀) (A₁F : A₁ ⥤ B₁)
    (B₀F : A₀ ⥤ C₀) (B₁F : A₁ ⥤ C₁)
    (P₀ : C₀ ⥤ B₀) (P₁ : C₁ ⥤ B₁)
    (F : A ⥤ B) (G : A ⥤ C) (H : C ⥤ B)
    (bA : A₀F ⋙ TY ≅ TX ⋙ A₁F)
    (bB : B₀F ⋙ TZ ≅ TX ⋙ B₁F)
    (bP : P₀ ⋙ TY ≅ TZ ⋙ P₁)
    (a₀ : A₀F ⋙ IY₀ ≅ IX₀ ⋙ F) (a₁ : A₁F ⋙ IY₁ ≅ IX₁ ⋙ F)
    (b₀ : B₀F ⋙ IZ₀ ≅ IX₀ ⋙ G) (b₁ : B₁F ⋙ IZ₁ ≅ IX₁ ⋙ G)
    (p₀ : P₀ ⋙ IY₀ ≅ IZ₀ ⋙ H) (p₁ : P₁ ⋙ IY₁ ≅ IZ₁ ⋙ H)
    (hA : ∀ K, IY₁.map (bA.hom.app K) ≫ a₁.hom.app (TX.obj K) =
      tY.hom.app (A₀F.obj K) ≫ a₀.hom.app K ≫ F.map (tX.inv.app K))
    (hB : ∀ K, IZ₁.map (bB.hom.app K) ≫ b₁.hom.app (TX.obj K) =
      tZ.hom.app (B₀F.obj K) ≫ b₀.hom.app K ≫ G.map (tX.inv.app K))
    (hP : ∀ L, IY₁.map (bP.hom.app L) ≫ p₁.hom.app (TZ.obj L) =
      tY.hom.app (P₀.obj L) ≫ p₀.hom.app L ≫ H.map (tZ.inv.app L))
    (r₀ : A₀F ≅ B₀F ⋙ P₀) (r₁ : A₁F ≅ B₁F ⋙ P₁)
    (hr : ∀ K, TY.map (r₀.hom.app K) ≫ bP.hom.app (B₀F.obj K) ≫
      P₁.map (bB.hom.app K) = bA.hom.app K ≫ r₁.hom.app (TX.obj K)) (K : A₀) :
    F.map (tX.inv.app K) ≫
        (a₁.inv.app (TX.obj K) ≫ IY₁.map (r₁.hom.app (TX.obj K)) ≫
          p₁.hom.app (B₁F.obj (TX.obj K)) ≫ H.map (b₁.hom.app (TX.obj K))) =
      (a₀.inv.app K ≫ IY₀.map (r₀.hom.app K) ≫ p₀.hom.app (B₀F.obj K) ≫
        H.map (b₀.hom.app K)) ≫ H.map (G.map (tX.inv.app K)) := by
  apply (cancel_epi (tY.hom.app (A₀F.obj K) ≫ a₀.hom.app K)).1
  simp only [Category.assoc]
  rw [← Category.assoc (a₀.hom.app K), ← Category.assoc (tY.hom.app _), ← hA K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← IY₁.map_comp_assoc, ← hr K, IY₁.map_comp, IY₁.map_comp]
  simp only [Category.assoc]
  have hp := p₁.hom.naturality (bB.hom.app K)
  dsimp only [Functor.comp_map] at hp
  rw [reassoc_of% hp, reassoc_of% (hP (B₀F.obj K))]
  have ht := tY.hom.naturality (r₀.hom.app K)
  dsimp only [Functor.comp_map] at ht
  rw [reassoc_of% ht]
  simp only [← H.map_comp]
  rw [hB K]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem morphism_transition
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, Category (A i)]
    {B : I → Type*} [∀ i, Category (B i)]
    {S : StageSystem A} {T : StageSystem B} (F : S.Morphism T)
    {i j : I} (hij : i ≤ j) (K : A i) :
    (T.ι j).map ((F.β hij).hom.app K) =
      (T.transIso hij).hom.app ((F.Φ i).obj K) ≫
        F.functor.map ((S.transIso hij).inv.app K) := by
  apply (cancel_epi ((T.transIso hij).inv.app ((F.Φ i).obj K))).1
  erw [Iso.inv_hom_id_app_assoc]
  change (T.isoToStage ⟨i, (F.Φ i).obj K⟩ hij).hom ≫ (T.ι j).map _ =
    F.functor.map (S.isoToStage ⟨i, K⟩ hij).hom
  dsimp only [StageSystem.isoToStage]
  erw [StageSystem.ι_map_eq (le_rfl : j ≤ j), F.functor_map_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  dsimp only [StageSystem.Morphism.mapAt]
  have hc := F.coh hij (le_rfl : j ≤ j) K
  have hc' := congrArg (fun t ↦
    ((T.assoc hij (le_rfl : j ≤ j)).inv.app ((F.Φ i).obj K)) ≫ t ≫
      (F.Φ j).map ((S.assoc hij (le_rfl : j ≤ j)).inv.app K) ≫
        (F.β (le_rfl : j ≤ j)).inv.app ((S.T hij).obj K)) hc
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hc'
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
    Category.comp_id, Iso.inv_hom_id_app_assoc] at hc'
  exact hc'

private theorem morphism_transition_with_inclusions
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, Category (A i)]
    {B : I → Type*} [∀ i, Category (B i)]
    {S : StageSystem A} {T : StageSystem B} (F : S.Morphism T)
    {i j : I} (hij : i ≤ j) (K : A i) :
    (T.ι j).map ((F.β hij).hom.app K) ≫
        (F.ιCompFunctorIso j).inv.app ((S.T hij).obj K) =
      (T.transIso hij).hom.app ((F.Φ i).obj K) ≫
        (F.ιCompFunctorIso i).inv.app K ≫
        F.functor.map ((S.transIso hij).inv.app K) := by
  simp only [StageSystem.Morphism.ιCompFunctorIso_inv_app]
  erw [Category.comp_id, Category.id_comp]
  exact morphism_transition F hij K

/-- Assemble a target comparison from the two inclusion cones and the finite scalar square.
Source: the common-stage coefficient-descent step of the exceptional-adjunction argument
(blueprint: lem-sf-stage-system-target-comparison).

Proof: compose the inverse first cone, inclusion of the finite comparison, the pullback
inclusion comparison, and the second cone whiskered by the descended functor. The
stage-morphism coherence equation computes the image of each transition. Paste this
square with the two cone squares and the finite scalar square. Naturality moves the
whiskered factors, and inverse cancellation gives the required compatibility. No
faithfulness, unit normalization, exactness or additional coherence is assumed. -/
theorem assembleTargetComparison
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, Category (A i)]
    {B : I → Type*} [∀ i, Category (B i)]
    {C : I → Type*} [∀ i, Category (C i)]
    (SX : StageSystem A) (SY : StageSystem B) (SZ : StageSystem C)
    (F : SX.PairCategory ⥤ SY.PairCategory) (G : SX.PairCategory ⥤ SZ.PairCategory)
    (P : SZ.Morphism SY) (Ai : ∀ i, A i ⥤ B i) (Bi : ∀ i, A i ⥤ C i)
    (bA : ∀ {i j}, (h : i ≤ j) → Ai i ⋙ SY.T h ≅ SX.T h ⋙ Ai j)
    (bB : ∀ {i j}, (h : i ≤ j) → Bi i ⋙ SZ.T h ≅ SX.T h ⋙ Bi j)
    (a : ∀ i, Ai i ⋙ SY.ι i ≅ SX.ι i ⋙ F)
    (b : ∀ i, Bi i ⋙ SZ.ι i ≅ SX.ι i ⋙ G)
    (hA : ∀ {i j} (h : i ≤ j) K,
      (SY.ι j).map ((bA h).hom.app K) ≫ (a j).hom.app ((SX.T h).obj K) =
        (SY.transIso h).hom.app ((Ai i).obj K) ≫ (a i).hom.app K ≫
          F.map ((SX.transIso h).inv.app K))
    (hB : ∀ {i j} (h : i ≤ j) K,
      (SZ.ι j).map ((bB h).hom.app K) ≫ (b j).hom.app ((SX.T h).obj K) =
        (SZ.transIso h).hom.app ((Bi i).obj K) ≫ (b i).hom.app K ≫
          G.map ((SX.transIso h).inv.app K))
    (r : ∀ i, Ai i ≅ Bi i ⋙ P.Φ i)
    (hr : ∀ {i j} (h : i ≤ j) K,
      (SY.T h).map ((r i).hom.app K) ≫ (P.β h).hom.app ((Bi i).obj K) ≫
        (P.Φ j).map ((bB h).hom.app K) =
          (bA h).hom.app K ≫ (r j).hom.app ((SX.T h).obj K)) :
    ∃ q : ∀ i, SX.ι i ⋙ F ≅ SX.ι i ⋙ (G ⋙ P.functor),
      ∀ {i j} (h : i ≤ j) K,
        F.map ((SX.transIso h).inv.app K) ≫ (q j).hom.app ((SX.T h).obj K) =
          (q i).hom.app K ≫ (G ⋙ P.functor).map ((SX.transIso h).inv.app K) := by
  let q i := comparison_at_stage (Ai i) (Bi i) (P.Φ i) (SX.ι i) (SY.ι i) (SZ.ι i)
    F G P.functor (a i) (b i) (P.ιCompFunctorIso i).symm (r i)
  refine ⟨q, ?_⟩
  intro i j h K
  have ht := paste_target_comparison (SX.T h) (SY.T h) (SZ.T h)
    (SX.ι i) (SX.ι j) (SY.ι i) (SY.ι j) (SZ.ι i) (SZ.ι j)
    (SX.transIso h) (SY.transIso h) (SZ.transIso h)
    (Ai i) (Ai j) (Bi i) (Bi j) (P.Φ i) (P.Φ j) F G P.functor
    (bA h) (bB h) (P.β h) (a i) (a j) (b i) (b j)
    (P.ιCompFunctorIso i).symm (P.ιCompFunctorIso j).symm
    (hA h) (hB h) (morphism_transition_with_inclusions P h) (r i) (r j) (hr h) K
  simpa only [q, comparison_at_stage, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.comp_map] using ht

end CategoryTheory.StageSystem
