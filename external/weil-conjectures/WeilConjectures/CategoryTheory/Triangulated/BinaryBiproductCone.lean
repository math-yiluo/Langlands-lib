/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Cones of morphisms into a binary biproduct

In a pretriangulated category, the cone of a morphism `biprod.lift f g : X ⟶ Y ⊞ Y'` whose
first component `f` is an isomorphism is identified with `Y'`, compatibly with the two
biproduct inclusions. This is used to construct homotopy pushouts of quasi-isomorphisms.

## Main statements

- `CategoryTheory.Pretriangulated.exists_iso_of_distTriang_biprod_lift`
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasBinaryBiproducts C]

/-- In a distinguished triangle `X ⟶ Y ⊞ Y' ⟶ Z ⟶ X⟦1⟧` whose first morphism is
`biprod.lift f g` with `f` an isomorphism, there is an isomorphism `θ : Z ≅ Y'` such that
`biprod.inr ≫ ψ ≫ θ.hom = 𝟙 Y'` and `biprod.inl ≫ ψ ≫ θ.hom = -(f⁻¹ ≫ g)`. -/
theorem exists_iso_of_distTriang_biprod_lift {X Y Y' Z : C} (f : X ⟶ Y) (g : X ⟶ Y')
    (ψ : Y ⊞ Y' ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift f g) ψ δ ∈ distTriang C) [IsIso f] :
    ∃ θ : Z ≅ Y', biprod.inr ≫ ψ ≫ θ.hom = 𝟙 Y' ∧
      biprod.inl ≫ ψ ≫ θ.hom = -(inv f ≫ g) := by
  let E : Y ⊞ Y' ≅ Y ⊞ Y' :=
    { hom := biprod.desc (biprod.lift (𝟙 Y) (-(inv f ≫ g))) biprod.inr
      inv := biprod.desc (biprod.lift (𝟙 Y) (inv f ≫ g)) biprod.inr
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  have hT' : Triangle.mk (biprod.lift f 0) (E.inv ≫ ψ) δ ∈ distTriang C :=
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) E.symm (Iso.refl _)
      (by apply biprod.hom_ext <;> simp [E]) (by simp) (by simp))
  have hT'' : Triangle.mk (biprod.lift f 0) (biprod.snd : Y ⊞ Y' ⟶ Y') 0 ∈ distTriang C :=
    isomorphic_distinguished _ (binaryBiproductTriangle_distinguished X Y') _
      (Triangle.isoMk _ _ (Iso.refl _) (biprod.mapIso (asIso f).symm (Iso.refl _)) (Iso.refl _)
        (by apply biprod.hom_ext <;> simp) (by apply biprod.hom_ext' <;> simp) (by simp))
  let e := isoTriangleOfIso₁₂ _ _ hT' hT'' (Iso.refl _) (Iso.refl _) (by simp)
  have h₂ : E.inv ≫ ψ ≫ e.hom.hom₃ = biprod.snd := by
    have := e.hom.comm₂
    simp only [e, isoTriangleOfIso₁₂_hom_hom₂] at this
    simpa [e] using this
  refine ⟨Triangle.π₃.mapIso e, ?_, ?_⟩
  · have : biprod.inr ≫ E.inv = (biprod.inr : Y' ⟶ Y ⊞ Y') := by simp [E]
    simp only [Functor.mapIso_hom, Triangle.π₃_map]
    rw [← this, assoc, h₂, biprod.inr_snd]
  · have : biprod.inl ≫ E.hom ≫ E.inv = (biprod.inl : Y ⟶ Y ⊞ Y') := by simp
    simp only [Functor.mapIso_hom, Triangle.π₃_map]
    rw [← this, assoc, assoc, h₂]
    simp [E]

end CategoryTheory.Pretriangulated
