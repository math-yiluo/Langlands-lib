/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar restriction of an open left mate -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory

/-- Pasting scalar restriction with a left mate gives the left mate of the
transported tensor comparison. Source: the unit form of the mates correspondence,
Stacks Tag 0GL6 (blueprint: lem-pur-restricted-open-mate-tensor).

Proof: transpose the composite under the first adjunction. Naturality moves the
unit past the scalar/tensor comparison. The unit equations for the two mates
replace the two open comparisons. Naturality of the restriction comparison and
of the scalar/tensor comparison leaves the inverse of the given pullback square.
Cancel its invertible factors. -/
theorem restricted_left_mate_tensor
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    (adj : J ⊣ P) (adj' : J' ⊣ P')
    (S : A ⥤ C) (S' : B ⥤ D) (U : C ⥤ A) (U' : D ⥤ B)
    (T : A ⥤ A) (T' : B ⥤ B)
    (e : S ⋙ U ≅ T) (e' : S' ⋙ U' ≅ T')
    (p : S' ⋙ P' ≅ P ⋙ S) (r : U' ⋙ P ≅ P' ⋙ U)
    (q : J ⋙ S' ≅ S ⋙ J') (o : U ⋙ J ≅ J' ⋙ U')
    (hq : ∀ K, S.map (adj.unit.app K) ≫ p.inv.app (J.obj K) =
      adj'.unit.app (S.obj K) ≫ P'.map (q.inv.app K))
    (ho : ∀ L, U.map (adj'.unit.app L) ≫ r.inv.app (J'.obj L) =
      adj.unit.app (U.obj L) ≫ P.map (o.hom.app L))
    (t : T' ⋙ P ≅ P ⋙ T)
    (h : ∀ L, r.hom.app (S'.obj L) ≫ U.map (p.hom.app L) ≫
      e.hom.app (P.obj L) = P.map (e'.hom.app L) ≫ t.hom.app L)
    (K : A) :
    J.map (e.inv.app K) ≫ o.hom.app (S.obj K) ≫
        U'.map (q.inv.app K) ≫ e'.hom.app (J.obj K) =
      (adj.homEquiv _ _).symm (T.map (adj.unit.app K) ≫ t.inv.app (J.obj K)) := by
  dsimp only [Functor.comp_obj, Functor.id_obj] at *
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [adj.unit_naturality_assoc, ← reassoc_of% (ho (S.obj K))]
  have hn := r.inv.naturality (q.inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← U.map_comp_assoc, ← hq, U.map_comp, Category.assoc]
  have he := e.inv.naturality (adj.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at he
  rw [← reassoc_of% he]
  congr 1
  apply (cancel_mono (t.hom.app (J.obj K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← h]
  simp only [Iso.inv_hom_id_app_assoc, ← U.map_comp_assoc, Iso.inv_hom_id_app]
  all_goals simp only [Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app]

end CategoryTheory
