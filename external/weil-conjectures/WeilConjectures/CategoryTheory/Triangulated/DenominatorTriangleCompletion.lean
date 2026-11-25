/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Completing denominators to morphisms of distinguished triangles

Source: Stacks Project, Derived Categories, Tag 05R9 (lemma-limit-triangles),
construction over a prescribed denominator, in its incoming-arrow form
(blueprint: lem-pur-triangle-completion-ms6-05r9).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Every denominator into any vertex of a distinguished triangle extends to a morphism
from a distinguished triangle whose other two components are also denominators.
Source: Stacks Project, Derived Categories, Tag 05R9 (lemma-limit-triangles),
construction over a prescribed denominator, dualized to incoming arrows
(blueprint: lem-pur-triangle-completion-ms6-05r9).

Proof:
1. For `s : X' ⟶ T.obj₁`, TR1 of `def-weil-triangulated-category` gives a distinguished
   cone triangle on `s ≫ T.mor₁`, with second vertex `T.obj₂`.
2. The square with components `s` and the identity commutes. TR3 completes it to a
   triangle morphism. More precisely, choose the completion in the multiplicative system
   using MS6 of `def-pur-saturated-triangulated-localization`; MS1 puts the identity in
   the system. This gives the required first-vertex completion.
3. For the second and third vertices, rotate the triangle by TR2, apply the first-vertex
   construction, and rotate the resulting triangle morphism back. MS5 ensures membership
   in the system for all shifted components. The shift equivalences identify the prescribed
   vertex with the original object and the prescribed component with the original arrow.
-/
theorem denominator_triangle_completion
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C) :
    (∀ (X' : C) (s : X' ⟶ T.obj₁), S s →
      ∃ (Y' Z' : C) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ X'⟦(1 : ℤ)⟧),
        Triangle.mk f' g' h' ∈ distTriang C ∧
          ∃ φ : Triangle.mk f' g' h' ⟶ T,
            φ.hom₁ = s ∧ S φ.hom₂ ∧ S φ.hom₃) ∧
    (∀ (Y' : C) (s : Y' ⟶ T.obj₂), S s →
      ∃ (X' Z' : C) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ X'⟦(1 : ℤ)⟧),
        Triangle.mk f' g' h' ∈ distTriang C ∧
          ∃ φ : Triangle.mk f' g' h' ⟶ T,
            φ.hom₂ = s ∧ S φ.hom₁ ∧ S φ.hom₃) ∧
    (∀ (Z' : C) (s : Z' ⟶ T.obj₃), S s →
      ∃ (X' Y' : C) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ X'⟦(1 : ℤ)⟧),
        Triangle.mk f' g' h' ∈ distTriang C ∧
          ∃ φ : Triangle.mk f' g' h' ⟶ T,
            φ.hom₃ = s ∧ S φ.hom₁ ∧ S φ.hom₂) := by
  have : S.HasLeftCalculusOfFractions := hS.1.1
  have first : ∀ (X' : C) (s : X' ⟶ T.obj₁), S s →
      ∃ (Y' Z' : C) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
        (h' : Z' ⟶ X'⟦(1 : ℤ)⟧),
        Triangle.mk f' g' h' ∈ distTriang C ∧
          ∃ φ : Triangle.mk f' g' h' ⟶ T,
            φ.hom₁ = s ∧ S φ.hom₂ ∧ S φ.hom₃ := by
    intro X' s hs
    obtain ⟨Z', g', h', hZ⟩ := distinguished_cocone_triangle (s ≫ T.mor₁)
    let T' := Triangle.mk (s ≫ T.mor₁) g' h'
    obtain ⟨t, ht, h₂, h₃⟩ := MorphismProperty.compatible_with_triangulation
      T' T hZ hT s (𝟙 _) hs (S.id_mem _) (by simp [T'])
    refine ⟨T'.obj₂, T'.obj₃, T'.mor₁, T'.mor₂, T'.mor₃, hZ, ?_⟩
    exact ⟨Triangle.homMk _ _ s (𝟙 _) t (by simp [T']) h₂ h₃,
      rfl, S.id_mem _, ht⟩
  refine ⟨first, ?_, ?_⟩
  · intro Y' s hs
    obtain ⟨X', f', h', hX⟩ := distinguished_cocone_triangle₁ (s ≫ T.mor₂)
    let T' := Triangle.mk f' (s ≫ T.mor₂) h'
    obtain ⟨a, ha, ha₁, ha₂⟩ := MorphismProperty.compatible_with_triangulation
      T'.rotate T.rotate (rot_of_distTriang _ hX) (rot_of_distTriang _ hT)
      s (𝟙 _) hs (S.id_mem _) (by simp [T', Triangle.rotate])
    let b := (shiftFunctor C (1 : ℤ)).preimage a
    have hb : S b := by
      apply (MorphismProperty.IsCompatibleWithShift.iff S b (1 : ℤ)).mp
      simpa [b] using ha
    have hb₁ : T'.mor₁ ≫ s = b ≫ T.mor₁ := by
      apply (shiftFunctor C (1 : ℤ)).map_injective
      change (-(T'.mor₁⟦(1 : ℤ)⟧')) ≫ s⟦(1 : ℤ)⟧' =
        a ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) at ha₂
      rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj] at ha₂
      simpa only [Functor.map_comp, b, Functor.map_preimage] using! ha₂
    have hb₃ : T'.mor₃ ≫ b⟦(1 : ℤ)⟧' = (𝟙 _) ≫ T.mor₃ := by
      simpa [Triangle.rotate, b] using ha₁
    refine ⟨X', T.obj₃, f', s ≫ T.mor₂, h', hX, ?_⟩
    exact ⟨Triangle.homMk _ _ b s (𝟙 _) hb₁ (by simp) hb₃,
      rfl, hb, S.id_mem _⟩
  · intro Z' s hs
    obtain ⟨Y', f', g', hY⟩ := distinguished_cocone_triangle₂ (s ≫ T.mor₃)
    let T' := Triangle.mk f' g' (s ≫ T.mor₃)
    obtain ⟨b, hb, hb₁, hb₂⟩ := MorphismProperty.compatible_with_triangulation
      T'.invRotate T.invRotate (inv_rot_of_distTriang _ hY) (inv_rot_of_distTriang _ hT)
      (s⟦(-1 : ℤ)⟧') (𝟙 _) (S.shift hs _) (S.id_mem _) (by
        dsimp [T', Triangle.invRotate, Triangle.mk]
        simp only [Preadditive.comp_neg, ← Functor.map_comp_assoc, Functor.map_comp,
          Category.comp_id])
    have hb₃ : T'.mor₂ ≫ s = b ≫ T.mor₂ := by
      dsimp only [Triangle.invRotate, Triangle.mk] at hb₂
      rw [← cancel_mono ((shiftEquiv C (1 : ℤ)).counitIso.inv.app T.obj₃),
        Category.assoc, Category.assoc, ← hb₂]
      simp only [shiftEquiv'_counitIso, shift_neg_shift', Category.assoc,
        Iso.inv_hom_id_app_assoc]
    refine ⟨T.obj₁, Y', f', g', s ≫ T.mor₃, hY, ?_⟩
    exact ⟨Triangle.homMk _ _ (𝟙 _) b s hb₁ hb₃ (by simp),
      rfl, S.id_mem _, hb⟩

end CategoryTheory
