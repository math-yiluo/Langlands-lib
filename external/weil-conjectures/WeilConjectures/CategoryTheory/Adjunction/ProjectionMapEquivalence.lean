/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The projection map of an adjoint equivalence

Let `adj : F ⊣ G` be an adjunction with `F : D ⥤ C`, and let `φ : F (T_D a b) ⟶ T_C (F a) (F b)`
be a natural transformation of bifunctors. If `F` is an equivalence and `φ` is an isomorphism,
the right adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))`
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`) is an isomorphism
(`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isEquivalence`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The right adjoint projection map of an adjunction `F ⊣ G` whose left adjoint `F` is an
equivalence is an isomorphism as soon as the comparison `φ` is: its image under `F`, followed by
the invertible counit, is `φ` followed by `T_C` applied to the counit. -/
theorem isIso_rightAdjointProjectionMap_app_app_of_isEquivalence [F.IsEquivalence] [IsIso φ]
    (M : C) (L : D) : IsIso (((adj.rightAdjointProjectionMap φ).app M).app L) := by
  have : IsIso (F.map (((adj.rightAdjointProjectionMap φ).app M).app L)) := by
    have : IsIso (F.map (((adj.rightAdjointProjectionMap φ).app M).app L) ≫
        adj.counit.app _) := by
      rw [adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  exact isIso_of_reflects_iso _ F

end CategoryTheory.Adjunction
