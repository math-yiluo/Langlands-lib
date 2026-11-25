/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering

/-! # Component form of normalized descent

The categorical component calculation used for normalized integral pullback descent.
Source: Stacks Project, Tag 099N(5); normalized descent universal property
(blueprint: lem-pur-integral-pullback-descent-components).
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃
namespace CategoryTheory

/-- Rewrite a normalized descent universal property as equations on representatives.
Source: Stacks Project, Tag 099N(5), the categorical part of normalized descent
(blueprint: lem-pur-integral-pullback-descent-components).
Proof: apply the given universal property to G and c. Evaluate its compatibility
equation at each representative P, then cancel c(P) to obtain the component formula.
Conversely, compose every proposed component formula with c(P). Cancel the inverse
and apply natural-transformation extensionality to recover the full compatibility
equation. The uniqueness clause of the universal property then identifies the
proposed natural isomorphism. This uses only isomorphism cancellation, and therefore
also applies to zero objects or empty representative categories. -/
theorem normalizedDescentComponents_existsUnique
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (L : A ⥤ B) (F : B ⥤ C) (T : A ⥤ C) (e : L ⋙ F ≅ T)
    (universal : ∀ (G : B ⥤ C) (c : L ⋙ G ≅ T),
      ∃! i : F ≅ G, Functor.isoWhiskerLeft L i ≪≫ c = e)
    (G : B ⥤ C) (c : L ⋙ G ≅ T) :
    ∃! i : F ≅ G, ∀ P : A, i.app (L.obj P) = e.app P ≪≫ (c.app P).symm := by
  obtain ⟨i, hi, hu⟩ := universal G c
  refine ⟨i, ?_, ?_⟩
  · intro P
    apply Iso.ext
    apply (cancel_mono (c.app P).hom).1
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    have h := congrArg (fun z ↦ z.hom.app P) hi
    exact h
  · intro i' h'
    apply hu i'
    apply Iso.ext
    apply NatTrans.ext
    funext P
    have h := congrArg (fun z ↦ z.hom ≫ (c.app P).hom) (h' P)
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at h
    exact h

end CategoryTheory
