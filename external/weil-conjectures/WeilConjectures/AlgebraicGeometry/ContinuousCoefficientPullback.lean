/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientBasic
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Topology.Category.TopCat.Basic

/-! # Canonical pullback of continuous coefficient sections

Source: Bhatt--Scholze, Definition 6.8.1 and the paragraph before Definition 6.8.6.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Continuous postcomposition on coefficient sheaves. -/
noncomputable def continuousCoefficientMap {T S : Type (u + 1)}
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (φ : T →+* S) (hφ : Continuous φ) (X : Scheme.{u}) :
    continuousCoefficientSheaf X T ⟶ continuousCoefficientSheaf X S :=
  ⟨{ app U := CommRingCat.ofHom
       { toFun := fun f ↦ (⟨φ, hφ⟩ : C(T, S)).comp f
         map_one' := by ext; exact φ.map_one
         map_mul' := by intros; ext; exact φ.map_mul _ _
         map_zero' := by ext; exact φ.map_zero
         map_add' := by intros; ext; exact φ.map_add _ _ }
     naturality := by intros; rfl }⟩

end AlgebraicGeometry.Scheme
