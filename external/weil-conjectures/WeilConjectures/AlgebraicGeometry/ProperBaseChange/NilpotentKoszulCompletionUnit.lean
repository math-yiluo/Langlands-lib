/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NilpotentKoszulGradedTower
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.Algebra.Ring.GeomSum

/-! # Koszul completion at nilpotent generators
-/

@[expose] public section
-- This module only keeps a private proof helper.
set_option linter.privateModule false
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
namespace ProconstantRoos
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable (T : ℕᵒᵖ ⥤ A) (C : A)
  (u : (Functor.const ℕᵒᵖ).obj C ⟶ T)
  (v : T ⟶ (Functor.const ℕᵒᵖ).obj C)
  (huv : ∀ n : ℕ, u.app (op n) ≫ v.app (op n) = 𝟙 C)
  (a : ℕ) (hf : ∀ n : ℕ, T.map (homOfLE (Nat.le_add_right n a)).op =
    v.app (op (n + a)) ≫ u.app (op n))

private noncomputable def isLimit : IsLimit (Cone.mk C u) := by
  refine ⟨fun s ↦ s.π.app (op 0) ≫ v.app (op 0), ?_, ?_⟩
  · intro s j
    obtain ⟨n⟩ := j
    have hsn := s.w (homOfLE (Nat.le_add_right n a)).op
    have hsv := s.w (homOfLE (Nat.zero_le (n + a))).op
    have hv := v.naturality (homOfLE (Nat.zero_le (n + a))).op
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map] at hv
    rw [Category.comp_id] at hv
    change (s.π.app (op 0) ≫ v.app (op 0)) ≫ u.app (op n) = s.π.app (op n)
    rw [← hsv]
    simp only [Category.assoc]
    rw [reassoc_of% hv, ← hf n, hsn]
  · intro s m hm
    have h := hm (op 0)
    change m ≫ u.app (op 0) = s.π.app (op 0) at h
    rw [← h, Category.assoc, huv, Category.comp_id]

variable [HasProduct (fun n : ℕ ↦ T.obj (op n))] [HasProduct (fun _ : ℕ ↦ C)]

end ProconstantRoos
namespace ProconstantComplex
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
variable (D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (L : CochainComplex A ℤ)
  (w : (Functor.const ℕᵒᵖ).obj L ⟶ D)
  (β : ∀ p : ℤ, (D ⋙ HomologicalComplex.eval A (.up ℤ) p) ⟶
    (Functor.const ℕᵒᵖ).obj (L.X p))
  (hβ : ∀ n p, (w.app (op n)).f p ≫ (β p).app (op n) = 𝟙 (L.X p))
  (N : ℕ) (hN : ∀ n p,
    (D.map (homOfLE (Nat.le_add_right n N)).op).f p =
      (β p).app (op (n + N)) ≫ (w.app (op n)).f p)

end ProconstantComplex

universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
