/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData

/-! # Categorical pasting for trace transport -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
open CategoryTheory
namespace AlgebraicGeometry.Etale.SfP1Transport

private theorem transport_pasting
    {C D E W Z : Type*} [Category C] [Category D] [Category E]
    [Category W] [Category Z]
    (P : C ⥤ D) (Q : E ⥤ C) (F : E ⥤ D) (H : C ⥤ E)
    (R : Z ⥤ D) (R₀ : W ⥤ C) (U : W ⥤ Z) (V : C ⥤ W)
    (W₀ : D ⥤ Z) (T : D ⥤ E)
    (b : U ⋙ R ≅ R₀ ⋙ P) (d : H ⋙ Q ≅ V ⋙ R₀)
    (s : P ⋙ W₀ ≅ V ⋙ U) (e : T ⋙ F ≅ W₀ ⋙ R) (c : F ≅ Q ⋙ P)
    {B : C} {B' : D} {L : W} {K : Z}
    (a : U.obj L ≅ K) (v : V.obj B ≅ L) (l : P.obj B ≅ B')
    (k : W₀.obj B' ≅ K) (g : T.obj (P.obj B) ⟶ H.obj B)
    {J J' : E} {J₀ : C} {J₁ : D}
    (u : J ⟶ J') (uQ : Q.obj J ⟶ J₀) (uP : P.obj J₀ ⟶ J₁)
    (uF : F.obj J' ⟶ J₁) (τ : H.obj B ⟶ J)
    (hb : b.hom.app (V.obj B) ≫ P.map (d.inv.app B) =
      R.map (s.inv.app B) ≫ e.inv.app (P.obj B) ≫ F.map g ≫ c.hom.app (H.obj B))
    (ha : a.inv ≫ U.map v.inv ≫ s.inv.app B = k.inv ≫ W₀.map l.inv)
    (hu : c.hom.app J ≫ P.map uQ ≫ uP = F.map u ≫ uF) :
    R.map a.inv ≫ b.hom.app L ≫ P.map (R₀.map v.inv ≫ d.inv.app B) ≫
        P.map (Q.map τ ≫ uQ) ≫ uP =
      R.map k.inv ≫ e.inv.app B' ≫ F.map (T.map l.inv ≫ g ≫ τ ≫ u) ≫ uF := by
  have nb := b.hom.naturality v.inv
  have ne := e.inv.naturality l.inv
  have nc := c.hom.naturality τ
  simp only [Functor.comp_map] at nb ne nc
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% nb]
  rw [reassoc_of% hb]
  rw [← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, ha, R.map_comp_assoc]
  rw [reassoc_of% ne]
  rw [← reassoc_of% nc, hu]

/-- Naturality pastes geometric exchange, a coefficient square, and a unit square.
Source: the second triangle calculation in the projective-line adjunction proof.
The coefficient square first moves the inverse line comparison across exchange.
Naturality moves the arbitrary trace across pullback composition. The unit
square finishes the calculation, and forget-supports naturality identifies the
recorded direct-image factorization.
(auxiliary; not a blueprint node). -/
theorem traceTransportPasting
    {C D E W Z : Type*} [Category C] [Category D] [Category E]
    [Category W] [Category Z]
    (P : C ⥤ D) (Q : E ⥤ C) (F : E ⥤ D) (H : C ⥤ E)
    (R : Z ⥤ D) (R₀ : W ⥤ C) (U : W ⥤ Z) (V : C ⥤ W)
    (W₀ : D ⥤ Z) (T : D ⥤ E)
    (b : U ⋙ R ≅ R₀ ⋙ P) (d : H ⋙ Q ≅ V ⋙ R₀)
    (s : P ⋙ W₀ ≅ V ⋙ U) (e : T ⋙ F ≅ W₀ ⋙ R) (c : F ≅ Q ⋙ P)
    {B : C} {B' : D} {L : W} {K : Z}
    (a : U.obj L ≅ K) (v : V.obj B ≅ L) (l : P.obj B ≅ B')
    (k : W₀.obj B' ≅ K) (T₀ : D ⥤ E) (z : T ≅ T₀)
    (g : T₀.obj (P.obj B) ⟶ H.obj B)
    {J J' : E} {J₀ : C} {J₁ : D}
    (u : J ⟶ J') (uQ : Q.obj J ⟶ J₀) (uP : P.obj J₀ ⟶ J₁)
    (uF : F.obj J' ⟶ J₁) (τ : H.obj B ⟶ J)
    (hb : b.hom.app (V.obj B) ≫ P.map (d.inv.app B) =
      R.map (s.inv.app B) ≫ e.inv.app (P.obj B) ≫
        F.map (z.hom.app (P.obj B) ≫ g) ≫ c.hom.app (H.obj B))
    (ha : a.inv ≫ U.map v.inv ≫ s.inv.app B = k.inv ≫ W₀.map l.inv)
    (hu : c.hom.app J ≫ P.map uQ ≫ uP = F.map u ≫ uF) :
    middleComposite R b a ≫ P.map (R₀.map v.inv ≫ d.inv.app B) ≫
        P.map (Q.map τ ≫ uQ) ≫ uP =
      R.map k.inv ≫ e.inv.app B' ≫ F.map (traceComposite T T₀ z l g τ u) ≫ uF := by
  unfold middleComposite traceComposite
  have hn := z.hom.naturality l.inv
  have h := transport_pasting P Q F H R R₀ U V W₀ T b d s e c
    a v l k (z.hom.app (P.obj B) ≫ g) u uQ uP uF τ hb ha hu
  simpa only [Category.assoc, reassoc_of% hn] using h

end AlgebraicGeometry.Etale.SfP1Transport
