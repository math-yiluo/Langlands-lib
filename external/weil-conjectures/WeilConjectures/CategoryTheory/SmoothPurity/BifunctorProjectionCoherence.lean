/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # Shift and unit coherence for bifunctor isomorphisms

Source: Zheng, Theorem 2.18(2), natural-isomorphism cancellation for the shift
and unit equations (blueprint: lem-pur-bifunctor-projection-coherence).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace CategoryTheory

/-- Shift and unit coherence of a specified bifunctor isomorphism.
Source: the natural-isomorphism cancellation used in Zheng Theorem 2.18(2).
(blueprint: lem-pur-bifunctor-projection-coherence). -/
def BifunctorProjectionCoherent
    {D E F : Type*} [Category D] [Category E] [Category F]
    [HasShift E ℤ] [HasShift F ℤ]
    {T U : D ⥤ E ⥤ F} [sT : ∀ K, (T.obj K).CommShift ℤ]
    [sU : ∀ K, (U.obj K).CommShift ℤ]
    (e : T ≅ U) (σ : T ⟶ U) (J : E) (Q : D → F)
    (a : ∀ K, (U.obj K).obj J ⟶ Q K) (b : ∀ K, (T.obj K).obj J ⟶ Q K) : Prop :=
  e.hom = σ ∧ ∀ K,
    NatTrans.CommShift (e.hom.app K) ℤ ∧
    NatTrans.CommShift (e.inv.app K) ℤ ∧
    (e.hom.app K).app J ≫ a K = b K ∧
    (e.inv.app K).app J ≫ b K = a K

/-- Coherence of a natural isomorphism and its inverse from the forward equations.
Source: Zheng Theorem 2.18(2), natural-isomorphism cancellation.
(blueprint: lem-pur-bifunctor-projection-coherence).

Proof. Take the isomorphism of the given invertible transformation. Its inverse
commutes with shifts by inversion of the shift square. Substitute the forward unit
equation into the inverse one and cancel the inverse followed by the forward map. -/
theorem bifunctorIsoCoherence
    {D E F : Type*} [Category D] [Category E] [Category F]
    [HasShift E ℤ] [HasShift F ℤ]
    (T U : D ⥤ E ⥤ F) [sT : ∀ K, (T.obj K).CommShift ℤ]
    [sU : ∀ K, (U.obj K).CommShift ℤ]
    (σ : T ⟶ U) [IsIso σ] (J : E) (Q : D → F)
    (a : ∀ K, (U.obj K).obj J ⟶ Q K) (b : ∀ K, (T.obj K).obj J ⟶ Q K)
    (hs : ∀ K, NatTrans.CommShift (σ.app K) ℤ)
    (hu : ∀ K, (σ.app K).app J ≫ a K = b K) :
    ∃ e : T ≅ U, BifunctorProjectionCoherent e σ J Q a b := by
  let e := asIso σ
  refine ⟨e, rfl, fun K ↦ ?_⟩
  have h : NatTrans.CommShift (e.app K).hom ℤ := hs K
  refine ⟨hs K, NatTrans.CommShift.of_iso_inv (e.app K) ℤ, hu K, ?_⟩
  rw [← hu K]
  change (e.inv.app K).app J ≫ ((e.hom.app K).app J ≫ _) = _
  rw [← Category.assoc, Iso.inv_hom_id_app_app, Category.id_comp]

end CategoryTheory
