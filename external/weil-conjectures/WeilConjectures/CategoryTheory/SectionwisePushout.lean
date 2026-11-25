/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Sectionwise pushouts of sheaves

Source: Stacks Project, Tag 03EK; coefficient-twist blueprint, proof step 6.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A sectionwise pushout square of sheaves is a pushout square of sheaves.

Source: Stacks Project, Tag 03EK.
(auxiliary; not a blueprint node)

Proof: evaluation jointly reflects colimits of presheaves. The fully faithful
inclusion of sheaves into presheaves reflects colimits, so the sectionwise universal
properties give the required universal property among sheaves. No preservation of
colimits by the inclusion is asserted or required. -/
theorem sheaf_isPushout_of_sectionwise
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {D : Type w} [Category.{t} D]
    {A B M N : Sheaf J D} (a : A ⟶ B) (b : A ⟶ M)
    (c : B ⟶ N) (d : M ⟶ N) (h : a ≫ c = b ≫ d)
    (hs : ∀ U : Cᵒᵖ, IsPushout (a.hom.app U) (b.hom.app U)
      (c.hom.app U) (d.hom.app U)) : IsPushout a b c d := by
  let q := PushoutCocone.mk c d h
  apply IsPushout.of_isColimit (c := q)
  apply isColimitOfReflects (sheafToPresheaf J D)
  apply evaluationJointlyReflectsColimits
  intro U
  let qU := ((evaluation Cᵒᵖ D).obj U).mapCocone
    ((sheafToPresheaf J D).mapCocone q)
  refine (IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk qU)).symm ?_
  exact (hs U).isColimit

end CategoryTheory
