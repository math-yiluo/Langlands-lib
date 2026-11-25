/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-!
# Reflecting the invertibility of the projection map along a square of adjunctions

In the setting of `CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv` (a square
`α : N_D ⋙ F' ≅ F ⋙ N_C` between adjunctions `F ⊣ G` and `F' ⊣ G'`, with compatible comparisons),
the image under `N_D` of the projection map of `F ⊣ G` at `(M, L)` is an isomorphism as soon as
the projection map of `F' ⊣ G'` at `(N_C M, N_D L)` is one and the base change map `β` (the mate of
`α`) is invertible at `M` and at `M ⊗ F L`
(`CategoryTheory.Adjunction.isIso_map_rightAdjointProjectionMap_of_mateEquiv`). This is the
converse direction of `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv`,
used to deduce a projection formula from its reductions.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  {N_D : D ⥤ D'} {N_C : C ⥤ C'} {α : N_D ⋙ F' ≅ F ⋙ N_C}
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
  {φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C}
  {φ' : (postcompose₂.obj F').obj T_D' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj T_C'}
  {m_C : (postcompose₂.obj N_C).obj T_C ≅ (((whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C'}
  {m_D : (postcompose₂.obj N_D).obj T_D ≅ (((whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D'}

/-- If the base change map `β` (the mate of `α`) is an isomorphism at `M` and at `M ⊗ F L`, and
the projection map of `adj'` is an isomorphism at `(N_C M, N_D L)`, then the image under `N_D` of
the projection map of `adj` at `(M, L)` is an isomorphism. -/
lemma isIso_map_rightAdjointProjectionMap_of_mateEquiv
    (H : ComparisonCompatible α φ φ' m_C m_D) (M : C) (L : D)
    (h : IsIso (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app (N_D.obj L)))
    (h₁ : IsIso ((mateEquiv adj adj' α.hom).app M))
    (h₂ : IsIso ((mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)))) :
    IsIso (N_D.map (((adj.rightAdjointProjectionMap φ).app M).app L)) := by
  have e := adj.map_rightAdjointProjectionMap_comp_mateEquiv adj' H M L
  have : IsIso (N_D.map (((adj.rightAdjointProjectionMap φ).app M).app L) ≫
      (mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)) ≫
        G'.map ((m_C.hom.app M).app (F.obj L) ≫ (T_C'.obj (N_C.obj M)).map (α.inv.app L))) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)) ≫
      G'.map ((m_C.hom.app M).app (F.obj L) ≫ (T_C'.obj (N_C.obj M)).map (α.inv.app L)))

end CategoryTheory.Adjunction
