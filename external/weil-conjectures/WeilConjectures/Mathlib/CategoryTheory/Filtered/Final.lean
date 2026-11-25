/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Colimits over weakly initial full subcategories

If `F : C ⥤ D` is fully faithful, `D` is cofiltered and every object of `D` receives a morphism
from an object in the image of `F`, then `C` is cofiltered, `F` is initial, and colimits of
diagrams indexed by `Dᵒᵖ` can be computed after restriction along `F.op`. Moreover, colimits of
diagrams indexed by equivalent categories agree.
-/

@[expose] public section

namespace CategoryTheory

open Limits

/-- **Colimits over a weakly initial full subcategory of a cofiltered category.** Let
`F : C ⥤ D` be fully faithful with `D` cofiltered, such that every object of `D` receives a
morphism from an object in the image of `F`. Then `C` is cofiltered, `F` is initial, and for any
`G : Dᵒᵖ ⥤ E` the colimit of `F.op ⋙ G` exists if and only if the colimit of `G` exists, in which
case the canonical map `colim (F.op ⋙ G) ⟶ colim G` is an isomorphism.

(blueprint: `lem-weil-pbc-colimit-initial-full-subcategory`) -/
theorem Functor.isCofiltered_initial_and_isIso_colimitPre {C D E : Type*} [Category C]
    [Category D] [Category E] (F : C ⥤ D) [IsCofiltered D] [F.Full] [F.Faithful]
    (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) (G : Dᵒᵖ ⥤ E) :
    IsCofiltered C ∧ F.Initial ∧ (HasColimit (F.op ⋙ G) ↔ HasColimit G) ∧
      ∀ _ : HasColimit G, ∃ _ : HasColimit (F.op ⋙ G), IsIso (colimit.pre G F.op) := by
  have := Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful F h
  exact ⟨IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful F h, this,
    Functor.Final.hasColimit_comp_iff _, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

/-- **Colimits over equivalent index categories.** If `e : J ≌ K` is an equivalence and
`w : e.functor ⋙ G ≅ F`, then there is an isomorphism `colim F ≅ colim G` whose composite with
the coprojection `ι_k` of `F` is `w⁻¹_k ≫ ι_{e k}`.

(blueprint: `lem-weil-pbc-colimit-initial-full-subcategory`) -/
theorem Limits.HasColimit.exists_iso_of_equivalence {J K C : Type*} [Category J] [Category K]
    [Category C] (e : J ≌ K) {G : K ⥤ C} {F : J ⥤ C} (w : e.functor ⋙ G ≅ F) [HasColimit F]
    [HasColimit G] :
    ∃ i : colimit F ≅ colimit G,
      ∀ k, colimit.ι F k ≫ i.hom = w.inv.app k ≫ colimit.ι G (e.functor.obj k) :=
  ⟨HasColimit.isoOfEquivalence e w, fun k ↦ by simp [HasColimit.ι_isoOfEquivalence_hom]⟩

end CategoryTheory
