/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness of the pair category

If all the categories `C i` of a stage system are idempotent complete, so is the pair category
`S.PairCategory`: an idempotent `e` of the pair category is represented at some stage `n` by `u`
with `u ≫ u = u` after a further transport, and the splitting of this idempotent at a finite
stage gives a splitting of `e`. Consequently the functor `toKaroubi` from the pair category to
its Karoubi envelope is an equivalence. This is the property of the `ℚ̄_ℓ`-category
`D^b_c(T, ℚ̄_ℓ)` deferred in its definition.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.exists_splitting`: an idempotent of the pair category
  splits through an object of a single stage.
- `CategoryTheory.StageSystem.PairCategory.isIdempotentComplete`: the pair category is
  idempotent complete.
- `CategoryTheory.StageSystem.PairCategory.isIdempotentComplete_and_isEquivalence_toKaroubi`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Idempotents

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] {S : StageSystem C}

namespace PairCategory

/-- An idempotent of the pair category which is conjugate to the image of an idempotent of
a stage `q`, under the inclusion `ι q`. -/
lemma exists_conj_ι_idem {X : S.PairCategory} (p : X ⟶ X) (hp : p ≫ p = p) :
    ∃ (q : I) (x : C q) (φ : X ≅ (S.ι q).obj x) (v : x ⟶ x), v ≫ v = v ∧
      p = φ.hom ≫ (S.ι q).map v ≫ φ.inv := by
  obtain ⟨n, -, hX, hX', u, rfl⟩ := exists_le_mkHom_eq p X.stage
  rw [mkHom_comp_mkHom, mkHom_eq_mkHom_iff] at hp
  obtain ⟨q, h, hu⟩ := hp
  refine ⟨q, (S.T h).obj (X.toStage hX),
    S.isoToStage X hX ≪≫ ((S.transIso h).app (X.toStage hX)).symm, (S.T h).map u, ?_, ?_⟩
  · rw [← Functor.map_comp, hu]
  · have := (S.transIso h).hom.naturality u
    simp only [Functor.comp_map] at this
    rw [mkHom_eq_isoToStage]
    simp [reassoc_of% this]

/-- Filtered retract descent, precise form: if all the stages are idempotent complete, every
idempotent of the pair category splits, through an object of a single stage. -/
lemma exists_splitting [∀ i, IsIdempotentComplete (C i)] {X : S.PairCategory} (p : X ⟶ X)
    (hp : p ≫ p = p) :
    ∃ (q : I) (y : C q) (i : (S.ι q).obj y ⟶ X) (e : X ⟶ (S.ι q).obj y),
      i ≫ e = 𝟙 _ ∧ e ≫ i = p := by
  obtain ⟨q, x, φ, v, hv, rfl⟩ := exists_conj_ι_idem p hp
  obtain ⟨y, i, e, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split x v hv
  refine ⟨q, y, (S.ι q).map i ≫ φ.inv, φ.hom ≫ (S.ι q).map e, ?_, ?_⟩
  · simp [← Functor.map_comp, h₁]
  · simp [← Functor.map_comp_assoc, h₂]

/-- Filtered retract descent: if all the stages of a stage system over a directed preorder are
idempotent complete, the pair category is idempotent complete. -/
instance isIdempotentComplete [∀ i, IsIdempotentComplete (C i)] :
    IsIdempotentComplete S.PairCategory where
  idempotents_split X p hp := by
    obtain ⟨q, y, i, e, h₁, h₂⟩ := exists_splitting p hp
    exact ⟨_, i, e, h₁, h₂⟩

/-- The Qbar-l category is idempotent complete. If all the stages are idempotent complete, the pair
category is idempotent complete and the canonical fully faithful functor to its Karoubi envelope is
an equivalence. (Its exactness, for triangulated stage systems, is
`CategoryTheory.StageSystem.PairCategory.isTriangulated_toKaroubi`.) -/
theorem isIdempotentComplete_and_isEquivalence_toKaroubi [∀ i, IsIdempotentComplete (C i)] :
    IsIdempotentComplete S.PairCategory ∧ (toKaroubi S.PairCategory).IsEquivalence :=
  ⟨inferInstance, inferInstance⟩

end PairCategory

end StageSystem

end CategoryTheory
