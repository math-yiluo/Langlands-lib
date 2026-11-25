/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Category.Preorder

set_option linter.privateModule false

/-!
# Normalization of coefficient comparisons

The categorical coherence argument used for Weil II (1.1.1) d).
(blueprint: lem-pod-lisse-fiber-coherence-normalization).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe d
open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

noncomputable section

private lemma liftIsoFromEnd {C D A : Type*} [Category C] [Category D] [Category A]
    (t : C ⥤ D) (F G : D ⥤ A) (a : F ≅ G)
    (h : Function.Bijective (fun u : F ⟶ F ↦ whiskerLeft t u))
    (e : t ⋙ F ≅ t ⋙ G) :
    ∃ u : F ≅ G, Functor.isoWhiskerLeft t u = e := by
  let q := e ≪≫ (Functor.isoWhiskerLeft t a).symm
  obtain ⟨u, hu⟩ := h.surjective q.hom
  obtain ⟨v, hv⟩ := h.surjective q.inv
  dsimp only at hu hv
  have huv : u ≫ v = 𝟙 F := h.injective (by
    change whiskerLeft t u ≫ whiskerLeft t v = 𝟙 _
    rw [hu, hv, q.hom_inv_id])
  have hvu : v ≫ u = 𝟙 F := h.injective (by
    change whiskerLeft t v ≫ whiskerLeft t u = 𝟙 _
    rw [hv, hu, q.inv_hom_id])
  let z : F ≅ F := ⟨u, v, huv, hvu⟩
  refine ⟨z ≪≫ a, ?_⟩
  apply Iso.ext
  change whiskerLeft t u ≫ (Functor.isoWhiskerLeft t a).hom = e.hom
  rw [hu]
  ext X
  simp [q]

private lemma whiskerIsoInjectiveFromEnd {C D A : Type*}
    [Category C] [Category D] [Category A]
    (t : C ⥤ D) (F G : D ⥤ A) (a : F ≅ G)
    (h : Function.Injective (fun u : F ⟶ F ↦ whiskerLeft t u)) :
    Function.Injective (fun u : F ≅ G ↦ Functor.isoWhiskerLeft t u) := by
  intro u v huv
  dsimp only at huv
  have he : u.hom ≫ a.inv = v.hom ≫ a.inv := h (by
    change (Functor.isoWhiskerLeft t u).hom ≫ whiskerLeft t a.inv =
      (Functor.isoWhiskerLeft t v).hom ≫ whiskerLeft t a.inv
    rw [huv])
  apply Iso.ext
  exact (cancel_mono a.inv).mp he

end

end CategoryTheory
