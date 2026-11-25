/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-!
# Reflecting the invertibility of a projection map along a conservative functor

In the setting of `CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`,
a functor `N_D` carries the projection map of `adj : F ⊣ G` to the projection map of
`adj' : F' ⊣ G'`, up to the tensor comparisons and the base change map `β`. If `N_D` reflects
isomorphisms, `β` is invertible at the relevant objects and the projection map of `adj'` is
invertible, then so is the projection map of `adj`. This transfers a projection formula from a
category in which it is known (e.g. condensed `ℓ`-adic sheaves) to one mapping to it by a
conservative functor (e.g. Weil complexes, by forgetting the Weil structure).

## Main results

- `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv_of_reflects`.
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

/-- If `N_D` reflects isomorphisms, the base change map `β` (the mate of `α`) is invertible at
`M` and at `M ⊗ F L`, and the projection map of `adj'` is invertible at `(N_C M, N_D L)`, then
the projection map of `adj` is invertible at `(M, L)`. -/
lemma isIso_rightAdjointProjectionMap_of_mateEquiv_of_reflects [N_D.ReflectsIsomorphisms]
    (H : ComparisonCompatible α φ φ' m_C m_D) (M : C) (L : D)
    [IsIso ((mateEquiv adj adj' α.hom).app M)]
    [IsIso ((mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)))]
    [IsIso (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app (N_D.obj L))] :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app L) := by
  have h := adj.map_rightAdjointProjectionMap_comp_mateEquiv adj' H M L
  have : IsIso (N_D.map (((adj.rightAdjointProjectionMap φ).app M).app L) ≫
      (mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)) ≫
        G'.map ((m_C.hom.app M).app (F.obj L) ≫
          (T_C'.obj (N_C.obj M)).map (α.inv.app L))) := by
    rw [h]
    infer_instance
  have : IsIso (N_D.map (((adj.rightAdjointProjectionMap φ).app M).app L)) :=
    IsIso.of_isIso_comp_right _ ((mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)) ≫
        G'.map ((m_C.hom.app M).app (F.obj L) ≫ (T_C'.obj (N_C.obj M)).map (α.inv.app L)))
  exact isIso_of_reflects_iso _ N_D

end CategoryTheory.Adjunction
