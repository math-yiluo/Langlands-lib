/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Cones of natural endomorphisms commute with products

Let `C` be a pretriangulated category and `H : C ⥤ C` a functor which is a *natural cone* of the
multiplication by an integer `m`: there are natural transformations `η : 𝟭 ⟶ H` and
`δ : H ⟶ [1]` such that `K --m--> K --η--> H K --δ--> K⟦1⟧` is distinguished for every `K`.
Then `H` preserves all products which exist in `C`
(`CategoryTheory.Pretriangulated.preservesLimit_discrete_of_distTriang`): the comparison map
`H(∏ Kⱼ) ⟶ ∏ H Kⱼ` is the third component of a morphism of distinguished triangles whose first two
components are isomorphisms.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A functor `H` which is a natural cone of the multiplication by an integer `m`, i.e. with
natural distinguished triangles `K --m--> K --η--> H K --δ--> K⟦1⟧`, preserves products. -/
lemma preservesLimit_discrete_of_distTriang (H : C ⥤ C) (m : ℤ) (η : 𝟭 C ⟶ H)
    (δ : H ⟶ shiftFunctor C (1 : ℤ))
    (hT : ∀ K, Triangle.mk (m • 𝟙 K) (η.app K) (δ.app K) ∈ distTriang C)
    {J : Type*} [HasLimitsOfShape (Discrete J) C] (K : J → C) :
    PreservesLimit (Discrete.functor K) H := by
  let T : J → Triangle C := fun j ↦ Triangle.mk (m • 𝟙 (K j)) (η.app (K j)) (δ.app (K j))
  have hc (j : J) : (m • 𝟙 (∏ᶜ K)) ≫ Pi.π K j = Pi.π K j ≫ (m • 𝟙 (K j)) := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, id_comp, comp_id]
  let φ (j : J) : Triangle.mk (m • 𝟙 (∏ᶜ K)) (η.app (∏ᶜ K)) (δ.app (∏ᶜ K)) ⟶ T j :=
    Triangle.homMk _ _ (Pi.π K j) (Pi.π K j) (H.map (Pi.π K j))
      (hc j) (η.naturality (Pi.π K j)).symm (δ.naturality (Pi.π K j)).symm
  let ψ := productTriangle.lift T φ
  have h₁ : IsIso ψ.hom₁ := by
    have : ψ.hom₁ = 𝟙 _ := Pi.hom_ext _ _ fun j ↦ by
      simp [ψ, φ, T]
    rw [this]
    infer_instance
  have h₂ : IsIso ψ.hom₂ := by
    have : ψ.hom₂ = 𝟙 _ := Pi.hom_ext _ _ fun j ↦ by
      simp [ψ, φ, T]
    rw [this]
    infer_instance
  have : IsIso ψ.hom₃ := isIso₃_of_isIso₁₂ ψ (hT _) (productTriangle_distinguished T fun j ↦ hT _)
    h₁ h₂
  have : IsIso (piComparison H K) := by
    have : piComparison H K = ψ.hom₃ := Pi.hom_ext _ _ fun j ↦ by
      simp only [piComparison_comp_π]
      exact (Pi.lift_comp_π (fun j ↦ H.map (Pi.π K j)) j).symm
    rw [this]
    infer_instance
  exact PreservesProduct.of_iso_comparison H K

end CategoryTheory.Pretriangulated
