/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Detecting isomorphisms of natural transformations on cones of an endomorphism

Let `τ : F ⟶ G` be a natural transformation between triangulated functors `C ⥤ D`, and let
`a : K ⟶ K` be an endomorphism killed by both `F` and `G`. If `τ` is an isomorphism at the
cones of `a` and of `a ≫ a`, then `τ` is an isomorphism at `K`
(`CategoryTheory.Functor.isIso_app_of_isIso_app_cones`).

The intended application is `a = ϖ • 𝟙 K` for an element `ϖ` of the coefficient ring, and `F`,
`G` followed by the reduction `- ⊗ᴸ Λ/ϖ`, which kills `ϖ`: then the statement says that a
natural transformation which is an isomorphism on `ϖ`-torsion objects becomes an isomorphism
after reduction modulo `ϖ`. No compatibility of `τ` with the shifts is needed.

## Proof

Let `K →a K →v₁ K₁ →w₁ K⟦1⟧` and `K →a≫a K →v₂ K₂ →w₂ K⟦1⟧` be the two triangles. The
obstruction `G v₁ ≫ τ_{K₁}⁻¹ ≫ F w₁ : G K ⟶ F (K⟦1⟧)` factors through `F (a⟦1⟧) = 0`, by
naturality of `τ` along a morphism of triangles `(a, 𝟙, ρ)` from the second triangle to the first
one. So `G v₁ ≫ τ_{K₁}⁻¹` lifts along `F v₁` to some `s : G K ⟶ F K`, and `s` is a two-sided
inverse of `τ_K`: the defects `s ≫ τ_K - 𝟙` and `τ_K ≫ s - 𝟙` are killed by `G v₁`, resp. `F v₁`,
hence factor through `G a = 0`, resp. `F a = 0`.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category Limits Pretriangulated

section

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive D]

/-- A functor commuting with the shifts which kills a morphism kills its shifts. -/
lemma map_shift_map_eq_zero (F : C ⥤ D) [F.CommShift ℤ] {K L : C} {a : K ⟶ L}
    (ha : F.map a = 0) (n : ℤ) : F.map (a⟦n⟧') = 0 := by
  have := (F.commShiftIso n).hom.naturality a
  dsimp at this
  rw [ha, Functor.map_zero, comp_zero] at this
  rwa [← cancel_mono ((F.commShiftIso n).hom.app L), zero_comp]

end

variable {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]

/-- Let `τ : F ⟶ G` be a natural transformation between triangulated functors and `a : K ⟶ K`
an endomorphism killed by `F` and `G`. If `τ` is an isomorphism at a cone `K₁` of `a` and at a
cone `K₂` of `a ≫ a`, then it is an isomorphism at `K`. -/
theorem isIso_app_of_isIso_app_cones (τ : F ⟶ G) {K K₁ K₂ : C} (a : K ⟶ K)
    (hFa : F.map a = 0) (hGa : G.map a = 0) {v₁ : K ⟶ K₁} {w₁ : K₁ ⟶ K⟦(1 : ℤ)⟧}
    {v₂ : K ⟶ K₂} {w₂ : K₂ ⟶ K⟦(1 : ℤ)⟧} (hT₁ : Triangle.mk a v₁ w₁ ∈ distTriang C)
    (hT₂ : Triangle.mk (a ≫ a) v₂ w₂ ∈ distTriang C)
    [IsIso (τ.app K₁)] [IsIso (τ.app K₂)] : IsIso (τ.app K) := by
  obtain ⟨ρ, hρ₁, hρ₂⟩ : ∃ ρ : K₂ ⟶ K₁, v₂ ≫ ρ = v₁ ∧ w₂ ≫ a⟦(1 : ℤ)⟧' = ρ ≫ w₁ := by
    obtain ⟨ρ, h₁, h₂⟩ := complete_distinguished_triangle_morphism _ _ hT₂ hT₁ a (𝟙 K)
      (comp_id _)
    exact ⟨ρ, h₁.trans (id_comp _), h₂⟩
  have hnat : CategoryTheory.inv (τ.app K₂) ≫ F.map ρ =
      G.map ρ ≫ CategoryTheory.inv (τ.app K₁) := by
    rw [IsIso.inv_comp_eq, ← τ.naturality_assoc, IsIso.hom_inv_id, comp_id]
  -- the obstruction `G v₁ ≫ τ_{K₁}⁻¹ ≫ F w₁` vanishes
  have hκ : G.map v₁ ≫ CategoryTheory.inv (τ.app K₁) ≫ F.map w₁ = 0 := by
    rw [← hρ₁, G.map_comp, assoc, ← reassoc_of% hnat, ← F.map_comp, ← hρ₂, F.map_comp,
      map_shift_map_eq_zero F hFa, comp_zero, comp_zero, comp_zero]
  have hTF : Triangle.mk (F.map a) (F.map v₁) (F.map w₁ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ∈
      distTriang D := F.map_distinguished _ hT₁
  have hTG : Triangle.mk (G.map a) (G.map v₁) (G.map w₁ ≫ (G.commShiftIso (1 : ℤ)).hom.app K) ∈
      distTriang D := G.map_distinguished _ hT₁
  obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ _ hTF
    (G.map v₁ ≫ CategoryTheory.inv (τ.app K₁)) (by simp [reassoc_of% hκ])
  simp only [Triangle.mk_mor₂] at hs
  have h₁ : s ≫ τ.app K = 𝟙 _ := by
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hTG (s ≫ τ.app K - 𝟙 _) (by
      simp only [Triangle.mk_mor₂]
      rw [Preadditive.sub_comp, assoc, ← τ.naturality, ← reassoc_of% hs, IsIso.inv_hom_id, comp_id,
        id_comp, sub_self])
    simp only [Triangle.mk_mor₁] at hg
    rw [hGa, comp_zero, sub_eq_zero] at hg
    exact hg
  have h₂ : τ.app K ≫ s = 𝟙 _ := by
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hTF (τ.app K ≫ s - 𝟙 _) (by
      simp only [Triangle.mk_mor₂]
      rw [Preadditive.sub_comp, assoc, ← hs, ← τ.naturality_assoc, IsIso.hom_inv_id, comp_id,
        id_comp, sub_self])
    simp only [Triangle.mk_mor₁] at hg
    rw [hFa, comp_zero, sub_eq_zero] at hg
    exact hg
  exact ⟨s, h₂, h₁⟩

end CategoryTheory.Functor
