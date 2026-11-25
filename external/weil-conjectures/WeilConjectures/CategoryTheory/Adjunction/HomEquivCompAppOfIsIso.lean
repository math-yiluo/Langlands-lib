/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.HomCongr

/-! # Hom-equivalences of an adjunction postcomposed with a partial isomorphism

Postcomposing the hom-equivalences of `L ⊣ R` with a transformation `R ⟶ R'` invertible on
a full subcategory of the target gives hom-equivalences `(L K ⟶ M) ≃ (K ⟶ R' M)` natural in `M`
in that subcategory (`CategoryTheory.Adjunction.exists_homEquiv_comp_app_of_isIso`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

/-- Postcomposing the hom-equivalence of an adjunction `L ⊣ R` with a transformation
`χ : R ⟶ R'` that is invertible on a full subcategory gives hom-equivalences
`(L K ⟶ M) ≃ (K ⟶ R' M)`, natural in `M` in that subcategory. -/
lemma exists_homEquiv_comp_app_of_isIso {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (χ : R ⟶ R') (P : ObjectProperty D)
    (hχ : ∀ M, P M → IsIso (χ.app M)) (K : C) :
    ∃ e : ∀ M : P.FullSubcategory, (L.obj K ⟶ M.obj) ≃ (K ⟶ R'.obj M.obj),
      ∀ (M N : P.FullSubcategory) (f : M ⟶ N) (h : L.obj K ⟶ M.obj),
        e N (h ≫ f.hom) = e M h ≫ R'.map f.hom := by
  refine ⟨fun M ↦ (adj.homEquiv K M.obj).trans
    (Iso.homCongr (Iso.refl K) (@asIso _ _ _ _ (χ.app M.obj) (hχ M.obj M.property))), ?_⟩
  intro M N f h
  simp [Adjunction.homEquiv_naturality_right]

end CategoryTheory.Adjunction
