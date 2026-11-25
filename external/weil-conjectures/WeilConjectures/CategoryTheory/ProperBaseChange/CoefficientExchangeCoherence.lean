/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareExchange

/-! # Generic coherence equations for coefficient exchange -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- The pointwise adjunct equation, kept over abstract functors. -/
def coefficientAdjunctCondition
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {lf : B ⥤ A} {rf : A ⥤ B} {lg : B ⥤ D}
    {lp : D ⥤ C} {gp : A ⥤ C} {rp : C ⥤ D}
    (εf : rf ⋙ lf ⟶ 𝟭 A) (εp : rp ⋙ lp ⟶ 𝟭 C)
    (sq : lg ⋙ lp ⟶ lf ⋙ gp) (β : rf ⋙ lg ⟶ gp ⋙ rp) (K : A) : Prop :=
  lp.map (β.app K) ≫ εp.app (gp.obj K) =
    sq.app (rf.obj K) ≫ gp.map (εf.app K)

/-- The canonical square exchange satisfies its pointwise adjunct equation. -/
theorem coefficientAdjunctCondition_of_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {lf : B ⥤ A} {rf : A ⥤ B} {lg : B ⥤ D}
    {lp : D ⥤ C} {gp : A ⥤ C} {rp : C ⥤ D}
    (adj : lf ⊣ rf) (adjp : lp ⊣ rp)
    (sq : lg ⋙ lp ≅ lf ⋙ gp) (β : rf ⋙ lg ⟶ gp ⋙ rp)
    (h : β = Adjunction.squareExchange adj adjp lg gp sq) (K : A) :
    coefficientAdjunctCondition adj.counit adjp.counit sq.hom β K := by
  subst β
  exact Adjunction.squareExchange_map_counit adj adjp lg gp sq K

/-- Coherence of coefficient pullback comparisons around a geometric square. -/
def coefficientPullbackCube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {lf : B ⥤ A} {lg : B ⥤ D} {lp : D ⥤ C} {gp : A ⥤ C}
    {Lf : B' ⥤ A'} {Lg : B' ⥤ D'} {Lp : D' ⥤ C'} {Gp : A' ⥤ C'}
    {tA : A ⥤ A'} {tB : B ⥤ B'} {tC : C ⥤ C'} {tD : D ⥤ D'}
    (αf : ∀ V, tA.obj (lf.obj V) ≅ Lf.obj (tB.obj V))
    (αg : ∀ V, tD.obj (lg.obj V) ≅ Lg.obj (tB.obj V))
    (αp : ∀ V, tC.obj (lp.obj V) ≅ Lp.obj (tD.obj V))
    (αq : ∀ V, tC.obj (gp.obj V) ≅ Gp.obj (tA.obj V))
    (sqE : lg ⋙ lp ⟶ lf ⋙ gp) (sqΩ : Lg ⋙ Lp ⟶ Lf ⋙ Gp) (V : B) : Prop :=
  (αp (lg.obj V)).inv ≫ tC.map (sqE.app V) ≫ (αq (lf.obj V)).hom =
    Lp.map (αg V).hom ≫ sqΩ.app (tB.obj V) ≫ Gp.map (αf V).inv

end CategoryTheory
