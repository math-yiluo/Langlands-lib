/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.NatIso

/-! # Composition after inverting comparison counits
Source: the counit equation for left derived functors; Stacks Project, Tag 0D5S.
(blueprint: lem-pc-counit-comparison-composition). -/

@[expose] public section
open CategoryTheory
namespace CategoryTheory
set_option autoImplicit false

/-- Inverting compatible counits transfers underived composition to derived composition.
Source: Stacks Project, Tag 0D5S; naturality and cancellation of invertible counits.
(blueprint: lem-pc-counit-comparison-composition).
Proof: postcompose both sides by the direct counit. Its defining equation replaces
the derived comparison by the two successive counits and the underived comparison.
Cancel the first counit, move the model isomorphism through the second counit by
naturality, and cancel that counit. The remaining equation is the inverse of the
underived model-composition equation, after localization. -/
theorem counitComparisonComposition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (Tp : C₀ ⥤ C₁) (Tq : C₁ ⥤ C₂) (Tr : C₀ ⥤ C₂)
    (Dp : D₀ ⥤ D₁) (Dq : D₁ ⥤ D₂) (Dr : D₀ ⥤ D₂)
    (κ : Tp ⋙ Tq ≅ Tr) (c : Dp ⋙ Dq ≅ Dr)
    (εp : Q₀ ⋙ Dp ⟶ Tp ⋙ Q₁) (εq : Q₁ ⋙ Dq ⟶ Tq ⋙ Q₂)
    (εr : Q₀ ⋙ Dr ⟶ Tr ⋙ Q₂)
    (K₀ : C₀) (K₁ : C₁) (K₂ K₂' : C₂)
    (θp : Tp.obj K₀ ≅ K₁) (θq : Tq.obj K₁ ≅ K₂')
    (θr : Tr.obj K₀ ≅ K₂) (μ : K₂ ≅ K₂')
    [IsIso (εp.app K₀)] [IsIso (εq.app K₁)] [IsIso (εr.app K₀)]
    (hε : c.hom.app (Q₀.obj K₀) ≫ εr.app K₀ =
      Dq.map (εp.app K₀) ≫ εq.app (Tp.obj K₀) ≫ Q₂.map (κ.hom.app K₀))
    (hθ : Tq.mapIso θp ≪≫ θq = κ.app K₀ ≪≫ θr ≪≫ μ) :
    Q₂.mapIso μ ≪≫ (Q₂.mapIso θq.symm ≪≫ (asIso (εq.app K₁)).symm) ≪≫
        Dq.mapIso (Q₁.mapIso θp.symm ≪≫ (asIso (εp.app K₀)).symm) ≪≫
        c.app (Q₀.obj K₀) = Q₂.mapIso θr.symm ≪≫ (asIso (εr.app K₀)).symm := by
  apply Iso.ext
  apply (cancel_mono (εr.app K₀)).mp
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    asIso_inv, Functor.map_comp, Category.assoc]
  rw [hε]
  simp only [Functor.map_inv, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn := εq.naturality θp.inv
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (Dq.map (Q₁.map θp.inv)), hn]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hi := congrArg Iso.inv hθ
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hi
  have hs := congrArg (fun t ↦ Q₂.map (μ.hom ≫ t ≫ κ.hom.app K₀)) hi
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app,
    Category.comp_id, Functor.map_comp] using hs

/-- Conjugating every comparison by model isomorphisms preserves its composition law.
Source: naturality of functor composition comparisons; Stacks Project, Tag 0D5S.
(blueprint: lem-pc-counit-comparison-composition).
Proof: cancel the two adjacent middle-model isomorphisms. Move the initial-model
isomorphism through the natural composition comparison, and move the final-model
isomorphism through the scalar comparison. What remains is the original law. -/
theorem conjugateComparisonComposition
    {D₀ D₁ D₂ : Type*} [Category* D₀] [Category* D₁] [Category* D₂]
    (Dp : D₀ ⥤ D₁) (Dq : D₁ ⥤ D₂) (Dr : D₀ ⥤ D₂) (c : Dp ⋙ Dq ≅ Dr)
    {U₀ X₀ : D₀} {U₁ X₁ : D₁} {U₂ U₂' X₂ X₂' : D₂}
    (s₀ : U₀ ≅ X₀) (s₁ : U₁ ≅ X₁) (s₂ : U₂ ≅ X₂) (s₂' : U₂' ≅ X₂')
    (μU : U₂ ≅ U₂') (μX : X₂ ≅ X₂')
    (δp : X₁ ≅ Dp.obj X₀) (δq : X₂' ≅ Dq.obj X₁) (δr : X₂ ≅ Dr.obj X₀)
    (hμ : μU ≪≫ s₂' = s₂ ≪≫ μX)
    (hδ : μX ≪≫ δq ≪≫ Dq.mapIso δp ≪≫ c.app X₀ = δr) :
    μU ≪≫ (s₂' ≪≫ δq ≪≫ Dq.mapIso s₁.symm) ≪≫
        Dq.mapIso (s₁ ≪≫ δp ≪≫ Dp.mapIso s₀.symm) ≪≫ c.app U₀ =
      s₂ ≪≫ δr ≪≫ Dr.mapIso s₀.symm := by
  apply Iso.ext
  have hm := congrArg Iso.hom hμ
  have hd := congrArg Iso.hom hδ
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc] at hm hd ⊢
  rw [← Dq.map_comp_assoc s₁.inv s₁.hom]
  simp only [Iso.inv_hom_id, Dq.map_id, Category.id_comp]
  have hn := c.hom.naturality s₀.inv
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc μU.hom s₂'.hom, hm]
  simpa only [Category.assoc] using congrArg (fun t ↦ s₂.hom ≫ t ≫ Dr.map s₀.inv) hd

/-- Naturality survives conjugation by natural model isomorphisms.
Source: naturality of the two chart isomorphisms; Stacks Project, Tag 08DW.
(blueprint: lem-pc-counit-comparison-composition). -/
theorem conjugateComparisonNaturality
    {C D : Type*} [Category* C] [Category* D]
    (F G F' G' : C ⥤ D) (s : F ≅ F') (t : G ≅ G')
    {X Y : C} (f : X ⟶ Y) (δX : F'.obj X ≅ G'.obj X) (δY : F'.obj Y ≅ G'.obj Y)
    (h : F'.map f ≫ δY.hom = δX.hom ≫ G'.map f) :
    F.map f ≫ (s.app Y ≪≫ δY ≪≫ (t.app Y).symm).hom =
      (s.app X ≪≫ δX ≪≫ (t.app X).symm).hom ≫ G.map f := by
  calc
    F.map f ≫ s.hom.app Y ≫ δY.hom ≫ (t.inv.app Y) =
        s.hom.app X ≫ F'.map f ≫ δY.hom ≫ (t.inv.app Y) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ δY.hom ≫ t.inv.app Y)
        (s.hom.naturality f)
    _ = s.hom.app X ≫ δX.hom ≫ G'.map f ≫ (t.inv.app Y) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ s.hom.app X ≫ z ≫ t.inv.app Y) h
    _ = s.hom.app X ≫ δX.hom ≫ t.inv.app X ≫ G.map f := by
      simpa only [Category.assoc] using congrArg (fun z ↦ s.hom.app X ≫ δX.hom ≫ z)
        (t.inv.naturality f)
    _ = (s.app X ≪≫ δX ≪≫ (t.app X).symm).hom ≫ G.map f := by simp [Category.assoc]

/-- The inverse of a counit remains natural between objects where it is invertible.
Source: naturality of the counit; Stacks Project, Tag 0D5S.
(blueprint: lem-pc-counit-comparison-composition). -/
theorem inverseCounitNaturality
    {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
    (Q : C ⥤ D) (Q' : C' ⥤ D') (T : C ⥤ C') (L : D ⥤ D')
    (ε : Q ⋙ L ⟶ T ⋙ Q') {K N : C} (f : K ⟶ N)
    [IsIso (ε.app K)] [IsIso (ε.app N)] :
    Q'.map (T.map f) ≫ inv (ε.app N) = inv (ε.app K) ≫ L.map (Q.map f) := by
  apply (cancel_mono (ε.app N)).mp
  have h := ε.naturality f
  dsimp only [Functor.comp_map] at h
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [h]
  simp only [IsIso.inv_hom_id_assoc]

/-- Compose a natural inverse-counit comparison with a natural model comparison.
Source: naturality and the preceding inverse-counit identity; Stacks Project, Tag 08DW.
(blueprint: lem-pc-counit-comparison-composition). -/
theorem inverseCounitModelNaturality
    {A C C' D D' : Type*} [Category* A] [Category* C] [Category* C']
    [Category* D] [Category* D'] (Q : C ⥤ D) (Q' : C' ⥤ D')
    (T : C ⥤ C') (L : D ⥤ D') (F : A ⥤ C) (G : A ⥤ C')
    (θ : F ⋙ T ≅ G) (ε : Q ⋙ L ⟶ T ⋙ Q') {K N : A} (f : K ⟶ N)
    [IsIso (ε.app (F.obj K))] [IsIso (ε.app (F.obj N))] :
    (G ⋙ Q').map f ≫
        (Q'.mapIso (θ.app N).symm ≪≫ (asIso (ε.app (F.obj N))).symm).hom =
      (Q'.mapIso (θ.app K).symm ≪≫ (asIso (ε.app (F.obj K))).symm).hom ≫
        (F ⋙ Q ⋙ L).map f := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv,
    Iso.app_inv, Functor.comp_map, Category.assoc]
  have h := congrArg Q'.map (θ.inv.naturality f)
  dsimp only [Functor.comp_map] at h
  simp only [Functor.map_comp] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [inverseCounitNaturality Q Q' T L ε (F.map f)]

end CategoryTheory
