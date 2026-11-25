/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.AlgCat.TensorAlgebra
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.Sites.MonObj

/-! # Normalized lifting of sectionwise actions

proof.md`, first two sentences;
the expanded proof of `lem-sfb-section-action-internal`.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonoidalClosed
namespace CategoryTheory

/-- The prescribed sheafification-local maps are stable under tensor.
Source: the sheaf tensor in the node's setup (auxiliary; not a blueprint node).
Proof: use `presheaf_enrichedHoms_exist` for the essentially small site. The
presheaf tensor-Hom adjunction and the sheaf property of Hom into a sheaf show
stability under left tensor; symmetry gives stability under right tensor. -/
@[instance] theorem sfbSectionAction_isMonoidal
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : (J.W (A := AddCommGrpCat.{w})).IsMonoidal := by
  let h := presheaf_enrichedHoms_exist (C := C) (A := AddCommGrpCat.{w})
  let : ∀ F G : Cᵒᵖ ⥤ AddCommGrpCat.{w},
    Enriched.FunctorCategory.HasEnrichedHom AddCommGrpCat.{w} F G := h.1
  let : ∀ F G : Cᵒᵖ ⥤ AddCommGrpCat.{w},
    Enriched.FunctorCategory.HasFunctorEnrichedHom AddCommGrpCat.{w} F G := h.2
  infer_instance

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C)

variable {B : Sheaf J CommRingCat.{w}}

end CategoryTheory
