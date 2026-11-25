/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Diagonal factorization of a cone transition

The off-diagonal entry of a factorization square gives a nullhomotopy of its
mapping-cone transition, before localization or any inverse limit.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex

namespace HomologicalComplex

/-- A diagonal factoring both sides of a square gives a nullhomotopy of the cone map.
Source: Stacks Tags 014E--014F; the explicit mapping-cone differential.
(blueprint: lem-pur-diagonal-cone-transition-homotopy).
Proof: the homotopy in degree i is the second cone projection, followed by the
factorization in degree i, followed by the first cone inclusion in degree i-1.
The two mixed differential terms cancel by the chain-map equation of the diagonal.
Its other two terms are exactly the diagonal entries of the cone transition. -/
theorem diagonalConeTransitionHomotopy
    {T : Type*} [Category T] {A : Type*} [Category A] [Abelian A]
    {C D : CochainComplex (T ⥤ A) ℤ} (α : C ⟶ D)
    {m n : T} (t : m ⟶ n)
    (b : D.asFunctor.obj m ⟶ C.asFunctor.obj n)
    (h₁ : ∀ i : ℤ, (α.f i).app m ≫ b.f i = (C.X i).map t)
    (h₂ : ∀ i : ℤ, b.f i ≫ (α.f i).app n = (D.X i).map t) :
    Nonempty (Homotopy ((mappingCone α).asFunctor.map t) 0) := by
  classical
  let s : ∀ i j : ℤ,
      ((mappingCone α).asFunctor.obj m).X i ⟶
        ((mappingCone α).asFunctor.obj n).X j := fun i j ↦
    if h : i + (-1) = j then
      ((mappingCone.snd α).v i i (add_zero i)).app m ≫ b.f i ≫
        ((mappingCone.inl α).v i j h).app n
    else 0
  refine ⟨{ hom := s, zero := ?_, comm := ?_ }⟩
  · intro i j h
    dsimp only [s]
    apply dite_eq_right
    intro hij
    apply h
    change j + 1 = i
    omega
  · intro i
    rw [dNext_eq s (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq s (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)]
    dsimp only [s, asFunctor_map_f, asFunctor_obj_d, zero_f]
    rw [dite_eq_left (show i + 1 + (-1) = i by omega),
      dite_eq_left (show i + (-1) = i - 1 by omega)]
    change ((mappingCone α).X i).map t =
      ((mappingCone α).d i (i + 1)).app m ≫
          (((mappingCone.snd α).v (i + 1) (i + 1) (add_zero _)).app m ≫
            b.f (i + 1) ≫ ((mappingCone.inl α).v (i + 1) i (by omega)).app n) +
        (((mappingCone.snd α).v i i (add_zero i)).app m ≫ b.f i ≫
          ((mappingCone.inl α).v i (i - 1) (by omega)).app n) ≫
          ((mappingCone α).d (i - 1) i).app n + 0
    have hd := NatTrans.congr_app (mappingCone.d_snd_v α i (i + 1) rfl) m
    have hi := NatTrans.congr_app (mappingCone.inl_v_d α i (i - 1) (i + 1)
      (by omega) (by omega)) n
    have hid := NatTrans.congr_app (mappingCone.id_X α i (i + 1) rfl) m
    simp only [NatTrans.comp_app, NatTrans.app_add, NatTrans.app_sub,
      NatTrans.id_app] at hd hi hid
    have hdiag : ((mappingCone α).X i).map t =
        ((mappingCone.fst α).1.v i (i + 1) rfl).app m ≫
          (C.X (i + 1)).map t ≫ ((mappingCone.inl α).v (i + 1) i (by omega)).app n +
        ((mappingCone.snd α).v i i (add_zero i)).app m ≫
          (D.X i).map t ≫ ((mappingCone.inr α).f i).app n := by
      rw [((mappingCone.inl α).v (i + 1) i (by omega)).naturality t,
        ((mappingCone.inr α).f i).naturality t]
      simp only [← Category.assoc, ← Preadditive.add_comp, hid, Category.id_comp]
    have hb := b.comm i (i + 1)
    change b.f i ≫ (C.d i (i + 1)).app n =
      (D.d i (i + 1)).app m ≫ b.f (i + 1) at hb
    rw [← Category.assoc, hd]
    simp only [Preadditive.add_comp, Category.assoc, hi, Preadditive.comp_sub]
    rw [reassoc_of% h₁ (i + 1), reassoc_of% h₂ i, ← reassoc_of% hb]
    rw [hdiag]
    abel

end HomologicalComplex
