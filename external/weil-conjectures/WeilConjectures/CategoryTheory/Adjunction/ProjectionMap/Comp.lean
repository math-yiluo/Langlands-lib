/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The right adjoint projection map through a second adjunction

Let `adj : F ⊣ G` with `F : D ⥤ C` and let `adj' : Q ⊣ R` with `Q : C ⥤ D` be such that the
unit of the composite adjunction `F ⋙ Q ⊣ R ⋙ G` is an isomorphism; for instance `g^* ⊣ g_*`
and `i^* ⊣ i_*` for a section `i` of `g`. Composed with `G` of the unit of `adj'`, the right
adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))` is the unit of the composite adjunction
followed by `G R Q` of its transpose. This gives a criterion for the projection map to be an
isomorphism, `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_comp`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- **The right adjoint projection map through a second adjunction.** Let `adj' : Q ⊣ R` be an
adjunction with `Q : C ⥤ D` such that the unit of the composite adjunction
`F ⋙ Q ⊣ R ⋙ G` is an isomorphism. Then the right adjoint projection map at `(M, L)` is an
isomorphism as soon as `φ` is one at `(G M, L)`, `Q` carries `T_C (ε_M) (𝟙 (F L))` to an
isomorphism, and the unit of `adj'` is an isomorphism at `T_C M (F L)`.

The typical case is a section `i` of `g` that is open and closed, `F ⊣ G` being `g^* ⊣ g_*`,
`Q ⊣ R` being `i^* ⊣ i_*` and `M` an object supported on the image of `i`: composed with `G`
of the unit of `adj'`, the projection map is the unit of `F ⋙ Q ⊣ R ⋙ G` followed by `G R Q`
of the transpose of the projection map. -/
lemma isIso_rightAdjointProjectionMap_app_app_of_comp {Q : C ⥤ D} {R : D ⥤ C} (adj' : Q ⊣ R)
    [IsIso (adj.comp adj').unit] (M : C) (L : D) [IsIso ((φ.app (G.obj M)).app L)]
    [IsIso (Q.map ((T_C.map (adj.counit.app M)).app (F.obj L)))]
    [IsIso (adj'.unit.app ((T_C.obj M).obj (F.obj L)))] :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app L) := by
  have key : ((adj.rightAdjointProjectionMap φ).app M).app L ≫
      G.map (adj'.unit.app ((T_C.obj M).obj (F.obj L))) =
      (adj.comp adj').unit.app ((T_D.obj (G.obj M)).obj L) ≫
        G.map (R.map (Q.map ((φ.app (G.obj M)).app L ≫
          (T_C.map (adj.counit.app M)).app (F.obj L)))) := by
    rw [rightAdjointProjectionMap_app_app, homEquiv_unit, comp_unit_app]
    simp only [Category.assoc, ← G.map_comp]
    congr 2
    simp
  have : IsIso (Q.map ((φ.app (G.obj M)).app L ≫
      (T_C.map (adj.counit.app M)).app (F.obj L))) := by
    rw [Q.map_comp]
    infer_instance
  have : IsIso (((adj.rightAdjointProjectionMap φ).app M).app L ≫
      G.map (adj'.unit.app ((T_C.obj M).obj (F.obj L)))) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map (adj'.unit.app ((T_C.obj M).obj (F.obj L))))

end CategoryTheory.Adjunction
