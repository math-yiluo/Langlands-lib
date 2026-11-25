/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Fully faithful duals have invertible double-dual maps

Let `C` be a braided monoidal closed category, `W : C` and `D = [-, W]`. The contravariant
functor `D` is adjoint to itself on the right, with unit the double-dual map
`δ_A = toIhomIhom W A : A ⟶ D D A`. Concretely, maps `D A ⟶ D T` correspond to maps
`T ⊗ D A ⟶ W`, hence through the braiding to maps `D A ⊗ T ⟶ W`, hence to maps `T ⟶ D D A`; under
this bijection `D f` corresponds to `f ≫ δ_A`
(`CategoryTheory.MonoidalClosed.bijective_pre_app_iff`).

## Main results

- `CategoryTheory.MonoidalClosed.bijective_pre_app_of_isIso`: if `δ_A` is an isomorphism, then
  `f ↦ D f : (T ⟶ A) → (D A ⟶ D T)` is bijective.
- `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_of_bijective`: conversely, if
  `f ↦ D f` is bijective on `A ⟶ A` and on `D D A ⟶ A`, then `δ_A` is an isomorphism.
- `CategoryTheory.MonoidalClosed.bijective_pre_app_of_iso`: the bijectivity of `f ↦ D f` on
  `T ⟶ A` only depends on `T` up to isomorphism.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

/-- The bijectivity of the action of a functor on morphisms only depends on the source and the
target up to isomorphism. -/
lemma Functor.bijective_map_of_iso {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B A' B' : C} (e : A ≅ A') (e' : B ≅ B')
    (h : Function.Bijective (fun f : A ⟶ B ↦ F.map f)) :
    Function.Bijective (fun f : A' ⟶ B' ↦ F.map f) := by
  have : (fun f : A' ⟶ B' ↦ F.map f) =
      (F.mapIso e).homCongr (F.mapIso e') ∘ (fun f : A ⟶ B ↦ F.map f) ∘ (e.homCongr e').symm := by
    ext f
    simp [Iso.homCongr_apply]
  rw [this]
  exact ((F.mapIso e).homCongr (F.mapIso e')).bijective.comp
    (h.comp (e.homCongr e').symm.bijective)

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- An isomorphism `e : X ≅ Y` induces an isomorphism `[Y, W] ≅ [X, W]` of internal homs,
given by `pre e.hom` and `pre e.inv`. -/
@[simps]
noncomputable def preIso (W : C) {X Y : C} (e : X ≅ Y) : (ihom Y).obj W ≅ (ihom X).obj W where
  hom := (pre e.hom).app W
  inv := (pre e.inv).app W
  hom_inv_id := by simp [← NatTrans.comp_app, ← pre_map]
  inv_hom_id := by simp [← NatTrans.comp_app, ← pre_map]

/-- The map `f ↦ D f : (T ⟶ A) → (D A ⟶ D T)`, `D = [-, W]`, is bijective if and only if
`g ↦ g ≫ δ_A : (T ⟶ A) → (T ⟶ D D A)` is, `δ_A = toIhomIhom W A`: the two maps differ by the
bijection `(D A ⟶ D T) ≃ (T ⟶ D D A)` of the self-adjunction of `D`. -/
lemma bijective_pre_app_iff (W T A : C) :
    Function.Bijective (fun f : T ⟶ A ↦ (pre f).app W) ↔
      Function.Bijective (fun g : T ⟶ A ↦ g ≫ toIhomIhom W A) := by
  let φ : ((ihom A).obj W ⟶ (ihom T).obj W) → (T ⟶ (ihom ((ihom A).obj W)).obj W) :=
    fun h ↦ curry ((β_ _ T).hom ≫ uncurry h)
  have hφ : Function.Bijective φ := by
    refine ⟨fun h h' hh ↦ ?_, fun g ↦ ⟨curry ((β_ _ T).inv ≫ uncurry g), ?_⟩⟩
    · have := congrArg (fun x ↦ (β_ _ T).inv ≫ uncurry x) hh
      exact uncurry_injective (by simpa [φ] using this)
    · simp [φ]
  have : (fun g : T ⟶ A ↦ g ≫ toIhomIhom W A) = φ ∘ (fun f : T ⟶ A ↦ (pre f).app W) := by
    ext g
    simp only [Function.comp_apply, φ, uncurry_pre, toIhomIhom]
    rw [← BraidedCategory.braiding_naturality_right_assoc, curry_natural_left]
  rw [this, Function.Bijective.of_comp_iff' hφ]

/-- If the double-dual map `δ_A` is an isomorphism, then `f ↦ D f : (T ⟶ A) → (D A ⟶ D T)` is
bijective, `D = [-, W]`. -/
lemma bijective_pre_app_of_isIso (W T A : C) [IsIso (toIhomIhom W A)] :
    Function.Bijective (fun f : T ⟶ A ↦ (pre f).app W) := by
  rw [bijective_pre_app_iff]
  exact ((asIso (toIhomIhom W A)).homToEquiv (Z := T)).bijective

/-- The bijectivity of `f ↦ D f : (T ⟶ A) → (D A ⟶ D T)`, `D = [-, W]`, only depends on `T` up
to isomorphism. -/
lemma bijective_pre_app_of_iso (W : C) {T T' : C} (e : T ≅ T') (A : C)
    (h : Function.Bijective (fun f : T' ⟶ A ↦ (pre f).app W)) :
    Function.Bijective (fun f : T ⟶ A ↦ (pre f).app W) := by
  rw [bijective_pre_app_iff] at h ⊢
  have : (fun g : T ⟶ A ↦ g ≫ toIhomIhom W A) =
      e.homFromEquiv.symm ∘ (fun g : T' ⟶ A ↦ g ≫ toIhomIhom W A) ∘ e.homFromEquiv := by
    ext g
    simp [Iso.homFromEquiv]
  rw [this]
  exact e.homFromEquiv.symm.bijective.comp (h.comp e.homFromEquiv.bijective)

/-- **Fully faithful duals have invertible double-dual maps.** If `f ↦ D f`, `D = [-, W]`, is
bijective on `A ⟶ A` and on `D D A ⟶ A`, then the double-dual map `δ_A = toIhomIhom W A` is an
isomorphism. Through the self-adjunction of `D`, `f ↦ D f` becomes `g ↦ g ≫ δ_A`: surjectivity on
`D D A ⟶ A` gives a retraction `r` with `r ≫ δ_A = 𝟙`, and injectivity on `A ⟶ A` turns
`(δ_A ≫ r) ≫ δ_A = 𝟙 ≫ δ_A` into `δ_A ≫ r = 𝟙`. -/
theorem isIso_toIhomIhom_of_bijective (W A : C)
    (h₁ : Function.Bijective (fun f : A ⟶ A ↦ (pre f).app W))
    (h₂ : Function.Bijective
      (fun f : (ihom ((ihom A).obj W)).obj W ⟶ A ↦ (pre f).app W)) :
    IsIso (toIhomIhom W A) := by
  rw [bijective_pre_app_iff] at h₁ h₂
  obtain ⟨r, hr : r ≫ toIhomIhom W A = 𝟙 _⟩ := h₂.2 (𝟙 _)
  refine ⟨r, h₁.1 ?_, hr⟩
  simp only [Category.assoc, Category.id_comp]
  rw [hr, Category.comp_id]

end MonoidalClosed

end CategoryTheory
