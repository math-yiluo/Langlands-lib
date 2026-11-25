/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.CompatiblePlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Plus

/-!
# The multiequalizer functor of a cover as a limit functor

For a cover `S` of `X`, the functor `P ↦ multiequalizer (S.index P)` is isomorphic to
precomposition with the multicospan `(S.index (𝟭 Cᵒᵖ)).multicospan` followed by `lim`
(`CategoryTheory.GrothendieckTopology.Cover.multiequalizerFunctorIso`).
-/

@[expose] public section

universe w w' u v

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Cover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (D : Type w) [Category.{w'} D]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  {X : C} (S : J.Cover X) [HasLimitsOfShape (WalkingMulticospan S.shape) D]

/-- The functor `P ↦ multiequalizer (S.index P)` is the limit of the multicospan obtained by
precomposing `P` with the multicospan `(S.index (𝟭 Cᵒᵖ)).multicospan` in `Cᵒᵖ`. -/
noncomputable def multiequalizerFunctorIso :
    S.multiequalizerFunctor D ≅
      (Functor.whiskeringLeft _ _ D).obj (S.index (𝟭 Cᵒᵖ)).multicospan ⋙ lim :=
  NatIso.ofComponents (fun P ↦ HasLimit.isoOfNatIso (S.multicospanComp P (𝟭 Cᵒᵖ))) fun η ↦
    limit.hom_ext fun j ↦ by
      rcases j with I | I
      · simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_obj,
          MulticospanIndex.multicospan_obj_left, lim_obj, Category.assoc,
          HasLimit.isoOfNatIso_hom_π, multicospanComp_hom_app, Iso.refl_hom,
          multiequalizerFunctor_map_ι_assoc, Functor.comp_map, Functor.whiskeringLeft_obj_map,
          lim_map, limMap_π, Functor.whiskerLeft_app, HasLimit.isoOfNatIso_hom_π_assoc]
        exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
          (congrArg (_ ≫ ·) (Category.id_comp _)).symm
      · simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_obj,
          MulticospanIndex.multicospan_obj_right, lim_obj, Category.assoc,
          HasLimit.isoOfNatIso_hom_π, multicospanComp_hom_app, Iso.refl_hom,
          Functor.comp_map, Functor.whiskeringLeft_obj_map, lim_map, limMap_π,
          Functor.whiskerLeft_app, HasLimit.isoOfNatIso_hom_π_assoc]
        refine ((congrArg (_ ≫ ·) (Category.comp_id _)).trans ?_).trans
          (congrArg (_ ≫ ·) (Category.id_comp _)).symm
        rw [← limit.w _ (WalkingMulticospan.Hom.fst I),
          ← limit.w (S.index _).multicospan (WalkingMulticospan.Hom.fst I)]
        simp only [MulticospanIndex.multicospan_obj_left, MulticospanIndex.multicospan_obj_right,
          MulticospanIndex.multicospan_map_fst, index_fst, multiequalizerFunctor_map_ι_assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (η.naturality I.r.g₁.op).symm

end CategoryTheory.GrothendieckTopology.Cover
