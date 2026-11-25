/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import Mathlib.CategoryTheory.NatIso

/-! # Naturality of stagewise comparisons on the common-stage category -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.StageSystem

/-- Naturality on finite stages and their transition isomorphisms gives naturality
on every common-stage representative.
Source: the representative factorization in StageSystem.mkHom_eq_isoToStage.
(blueprint: lem-sf-stage-comparison-naturality).

Proof: write any common-stage arrow as the source isoToStage, the stage inclusion of
its representative, and the inverse target isoToStage. The compatibility equation gives
naturality for the source transition. Precompose the target compatibility with its
inverse to obtain naturality for the inverse target transition. Compose these equations
with naturality of the stagewise comparison on the middle representative. -/
theorem stageComparison_naturality
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {B : Type*} [Category B] (S : StageSystem C) (F H : S.PairCategory ⥤ B)
    (e : ∀ i, S.ι i ⋙ F ≅ S.ι i ⋙ H)
    (he : ∀ (A : S.PairCategory) (i : I) (h : A.stage ≤ i),
      F.map (S.isoToStage A h).hom ≫ (e i).hom.app (A.toStage h) =
        (e A.stage).hom.app A.obj ≫ H.map (S.isoToStage A h).hom)
    {A A' : S.PairCategory} (f : A ⟶ A') :
    F.map f ≫ (e A'.stage).hom.app A'.obj =
      (e A.stage).hom.app A.obj ≫ H.map f := by
  induction f using StageSystem.PairCategory.hom_induction with
  | h i hA hA' f =>
    have hright :
        F.map (S.isoToStage A' hA').inv ≫ (e A'.stage).hom.app A'.obj =
          (e i).hom.app (A'.toStage hA') ≫ H.map (S.isoToStage A' hA').inv := by
      apply (cancel_epi (F.map (S.isoToStage A' hA').hom)).1
      rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
      rw [← Category.assoc, he A' i hA']
      simp only [Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id]
      exact (Category.comp_id _).symm
    have hn := (e i).hom.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [StageSystem.mkHom_eq_isoToStage hA hA' f]
    simp only [Functor.map_comp, Category.assoc]
    rw [hright, reassoc_of% hn, reassoc_of% (he A i hA)]

end CategoryTheory.StageSystem
