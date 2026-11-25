/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope

/-!
# Compact objects are closed under extensions

In a pretriangulated category, if `T₁` and `T₃` are compact objects
(`CategoryTheory.BrownRepresentability.IsCompactObj`) and `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` is a
distinguished triangle, then `T₂` is compact
(`CategoryTheory.BrownRepresentability.IsCompactObj.of_distTriang`): this is the five lemma for
the maps `⨁ⱼ Hom(-, Xⱼ) ⟶ Hom(-, ∐ⱼ Xⱼ)`, which are always injective.

We also lift distinguished triangles of `C` with vertices in a triangulated subcategory `P` to
compact objects of the full subcategory
(`CategoryTheory.ObjectProperty.FullSubcategory.isCompactObj_of_distTriang`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated Category Preadditive

namespace CategoryTheory

namespace BrownRepresentability

variable {C : Type u} [Category.{v} C]

/-- In a preadditive category, if a finite sum `∑ⱼ gⱼ ≫ ιⱼ` of morphisms into a colimit cofan
vanishes, then each `gⱼ` vanishes. -/
lemma eq_zero_of_sum_comp_inj_eq_zero [Preadditive C] {J : Type*} {X : J → C} {c : Cofan X}
    (hc : IsColimit c) {s : C} (T : Finset J) (g : ∀ j, s ⟶ X j)
    (h : ∑ j ∈ T, g j ≫ c.inj j = 0) {j : J} (hj : j ∈ T) : g j = 0 := by
  classical
  have := h =≫ Cofan.IsColimit.desc hc (Pi.single (M := fun k ↦ X k ⟶ X j) j (𝟙 (X j)))
  rw [Preadditive.sum_comp, Finset.sum_eq_single j] at this
  · simpa using this
  · intro b _ hb
    rw [assoc, Cofan.IsColimit.fac, Pi.single_eq_of_ne hb, comp_zero]
  · exact fun h ↦ (h hj).elim

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Compact objects are closed under extensions: if `T` is a distinguished triangle whose first
and third objects are compact, then so is its second object. -/
lemma IsCompactObj.of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompactObj T.obj₁) (h₃ : IsCompactObj T.obj₃) : IsCompactObj T.obj₂ := by
  classical
  intro J X c hc f
  obtain ⟨S₁, a, ha⟩ := h₁ c hc (T.mor₁ ≫ f)
  let a' (j : J) : T.obj₁ ⟶ X j := if j ∈ S₁ then a j else 0
  have ha' : T.mor₁ ≫ f = ∑ j ∈ S₁, a' j ≫ c.inj j := by
    rw [ha]
    exact Finset.sum_congr rfl fun j hj ↦ by simp [a', hj]
  have hT' := inv_rot_of_distTriang _ hT
  have hw (j : J) : T.invRotate.mor₁ ≫ a' j = 0 := by
    by_cases hj : j ∈ S₁
    · refine eq_zero_of_sum_comp_inj_eq_zero hc S₁ (fun j ↦ T.invRotate.mor₁ ≫ a' j) ?_ hj
      simp only [assoc, ← comp_sum, ← ha']
      have h₀ : T.invRotate.mor₁ ≫ T.mor₁ = 0 := comp_distTriang_mor_zero₁₂ _ hT'
      rw [← assoc, h₀, zero_comp]
    · simp [a', hj]
  have hb (j : J) : ∃ b : T.obj₂ ⟶ X j, a' j = T.mor₁ ≫ b :=
    Triangle.yoneda_exact₂ _ hT' (a' j) (hw j)
  choose b hb using hb
  obtain ⟨g', hg'⟩ := Triangle.yoneda_exact₂ _ hT (f - ∑ j ∈ S₁, b j ≫ c.inj j) (by
    rw [comp_sub, ha', comp_sum]
    simp [hb])
  obtain ⟨S₃, e, he⟩ := h₃ c hc g'
  refine ⟨S₁ ∪ S₃, fun j ↦ (if j ∈ S₁ then b j else 0) + (if j ∈ S₃ then T.mor₂ ≫ e j else 0),
    ?_⟩
  simp only [add_comp, Finset.sum_add_distrib, ite_comp, zero_comp, Finset.sum_ite_mem,
    Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, assoc]
  rw [← comp_sum, ← he, ← hg', add_sub_cancel]

end BrownRepresentability

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  [P.IsTriangulated]

/-- Let `P` be a triangulated subcategory. If `Y ⟶ X ⟶ Z ⟶ Y⟦1⟧` is a distinguished triangle of
`C` with vertices in `P`, and `Y` and `Z` are compact objects of the full subcategory of `P`,
then so is `X`. -/
lemma FullSubcategory.isCompactObj_of_distTriang {Y X Z : P.FullSubcategory}
    (f : Y.obj ⟶ X.obj) (g : X.obj ⟶ Z.obj) (h : Z.obj ⟶ Y.obj⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C) (hY : BrownRepresentability.IsCompactObj Y)
    (hZ : BrownRepresentability.IsCompactObj Z) : BrownRepresentability.IsCompactObj X := by
  obtain ⟨W, g', h', hT'⟩ := distinguished_cocone_triangle (homMk f : Y ⟶ X)
  have hT'' : P.ι.mapTriangle.obj (Triangle.mk (homMk f) g' h') ∈ distTriang C := hT'
  obtain ⟨e, -⟩ := exists_iso_of_arrow_iso _ _ hT'' hT (Iso.refl _)
  exact BrownRepresentability.IsCompactObj.of_distTriang _ hT' hY
    (hZ.of_iso (P.fullyFaithfulι.preimageIso (Triangle.π₃.mapIso e)))

end ObjectProperty

end CategoryTheory
