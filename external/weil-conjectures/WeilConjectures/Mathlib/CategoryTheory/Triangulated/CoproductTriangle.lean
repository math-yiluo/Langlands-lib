/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Yoneda

/-!
# Coproducts of distinguished triangles

In a pretriangulated category, a coproduct of distinguished triangles is distinguished
(`CategoryTheory.Pretriangulated.coproductTriangle_distinguished`). This is dual to Mathlib's
`CategoryTheory.Pretriangulated.productTriangle_distinguished`, and the proof is the dual diagram
chase: comparing with a distinguished triangle on the coproduct of the first morphisms, the
induced map on third terms is shown to be bijective on morphisms out of it.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

namespace Pretriangulated

variable {C : Type*} [Category* C] [HasShift C ℤ] {J : Type*} (T : J → Triangle C)
  [HasCoproduct fun j ↦ (T j).obj₁] [HasCoproduct fun j ↦ (T j).obj₂]
  [HasCoproduct fun j ↦ (T j).obj₃] [HasCoproduct fun j ↦ (T j).obj₁⟦(1 : ℤ)⟧]

/-- The coproduct of a family of triangles. -/
noncomputable def coproductTriangle : Triangle C :=
  Triangle.mk (Limits.Sigma.map fun j ↦ (T j).mor₁) (Limits.Sigma.map fun j ↦ (T j).mor₂)
    (Limits.Sigma.map (fun j ↦ (T j).mor₃) ≫
      sigmaComparison (shiftFunctor C (1 : ℤ)) fun j ↦ (T j).obj₁)

/-- The inclusion of a summand into the coproduct of a family of triangles. -/
@[simps]
noncomputable def coproductTriangle.ι (j : J) : T j ⟶ coproductTriangle T where
  hom₁ := Sigma.ι (fun j ↦ (T j).obj₁) j
  hom₂ := Sigma.ι (fun j ↦ (T j).obj₂) j
  hom₃ := Sigma.ι (fun j ↦ (T j).obj₃) j
  comm₁ := by simp [coproductTriangle]
  comm₂ := by simp [coproductTriangle]
  comm₃ := by simp [coproductTriangle]

/-- A family of morphisms `T j ⟶ T'` induces a morphism `coproductTriangle T ⟶ T'`. -/
@[simps]
noncomputable def coproductTriangle.desc {T' : Triangle C} (φ : ∀ j, T j ⟶ T') :
    coproductTriangle T ⟶ T' where
  hom₁ := Sigma.desc fun j ↦ (φ j).hom₁
  hom₂ := Sigma.desc fun j ↦ (φ j).hom₂
  hom₃ := Sigma.desc fun j ↦ (φ j).hom₃
  comm₁ := Sigma.hom_ext _ _ fun j ↦ by simp [coproductTriangle]
  comm₂ := Sigma.hom_ext _ _ fun j ↦ by simp [coproductTriangle]
  comm₃ := Sigma.hom_ext _ _ fun j ↦ by
    simp [coproductTriangle]

variable [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- A coproduct of distinguished triangles is distinguished. -/
lemma coproductTriangle_distinguished (hT : ∀ j, T j ∈ distTriang C) :
    coproductTriangle T ∈ distTriang C := by
  let X₁ := ∐ fun j ↦ (T j).obj₁
  let X₂ := ∐ fun j ↦ (T j).obj₂
  let X₃ := ∐ fun j ↦ (T j).obj₃
  let m₁ : X₁ ⟶ X₂ := Limits.Sigma.map fun j ↦ (T j).mor₁
  let m₂ : X₂ ⟶ X₃ := Limits.Sigma.map fun j ↦ (T j).mor₂
  let m₃ : X₃ ⟶ X₁⟦(1 : ℤ)⟧ := Limits.Sigma.map (fun j ↦ (T j).mor₃) ≫
    sigmaComparison (shiftFunctor C (1 : ℤ)) fun j ↦ (T j).obj₁
  let ι₁ (j : J) : (T j).obj₁ ⟶ X₁ := Sigma.ι (fun j ↦ (T j).obj₁) j
  let ι₂ (j : J) : (T j).obj₂ ⟶ X₂ := Sigma.ι (fun j ↦ (T j).obj₂) j
  let ι₃ (j : J) : (T j).obj₃ ⟶ X₃ := Sigma.ι (fun j ↦ (T j).obj₃) j
  have hι₁₂ (j : J) : ι₁ j ≫ m₁ = (T j).mor₁ ≫ ι₂ j := by simp [ι₁, ι₂, m₁]
  have hι₂₃ (j : J) : ι₂ j ≫ m₂ = (T j).mor₂ ≫ ι₃ j := by simp [ι₂, ι₃, m₂]
  have hι₃₁ (j : J) : ι₃ j ≫ m₃ = (T j).mor₃ ≫ (ι₁ j)⟦(1 : ℤ)⟧' := by
    simp [ι₃, ι₁, m₃]
  obtain ⟨Z, f₂, f₃, hT'⟩ := distinguished_cocone_triangle m₁
  have ye₂ {A : C} (g : X₂ ⟶ A) (hg : m₁ ≫ g = 0) : ∃ h : Z ⟶ A, g = f₂ ≫ h :=
    Triangle.yoneda_exact₂ _ hT' g hg
  have ye₃ {A : C} (g : Z ⟶ A) (hg : f₂ ≫ g = 0) : ∃ h : X₁⟦(1 : ℤ)⟧ ⟶ A, g = f₃ ≫ h :=
    Triangle.yoneda_exact₃ _ hT' g hg
  have z₃₁ : f₃ ≫ m₁⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT'
  have hφ (j : J) : ∃ c : (T j).obj₃ ⟶ Z, (T j).mor₂ ≫ c = ι₂ j ≫ f₂ ∧
      (T j).mor₃ ≫ (ι₁ j)⟦(1 : ℤ)⟧' = c ≫ f₃ :=
    complete_distinguished_triangle_morphism _ _ (hT j) hT' (ι₁ j) (ι₂ j) (hι₁₂ j).symm
  choose c hc₂ hc₃ using hφ
  let ψ : X₃ ⟶ Z := Sigma.desc c
  have hι (j : J) : ι₃ j ≫ ψ = c j := by simp [ψ, ι₃]
  have hm₂ : m₂ ≫ ψ = f₂ := Sigma.hom_ext _ _ fun j ↦ by
    have := hι₂₃ j
    simp only [ι₂, ι₃] at this
    rw [reassoc_of% this, hι, hc₂]
  have hm₃ : m₃ = ψ ≫ f₃ := Sigma.hom_ext _ _ fun j ↦ by
    have := hι₃₁ j
    simp only [ι₃] at this
    rw [this, hc₃, ← hι j, assoc]
  have hc : IsColimit (Cofan.mk (X₁⟦(1 : ℤ)⟧) fun j ↦ (ι₁ j)⟦(1 : ℤ)⟧') :=
    isColimitCofanMkObjOfIsColimit (shiftFunctor C (1 : ℤ)) _ _ (coproductIsCoproduct _)
  have hc₂' : IsColimit (Cofan.mk (X₂⟦(1 : ℤ)⟧) fun j ↦ (ι₂ j)⟦(1 : ℤ)⟧') :=
    isColimitCofanMkObjOfIsColimit (shiftFunctor C (1 : ℤ)) _ _ (coproductIsCoproduct _)
  suffices IsIso ψ by
    refine isomorphic_distinguished _ hT' _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ψ) ?_ ?_ ?_)
    · exact (comp_id _).trans (id_comp _).symm
    · exact (hm₂.trans (id_comp _).symm)
    · simp only [Iso.refl_hom, asIso_hom, CategoryTheory.Functor.map_id, comp_id]
      exact hm₃
  refine isIso_of_coyoneda_map_bijective _ fun A ↦ ⟨fun g₁ g₂ hg ↦ ?_, fun a ↦ ?_⟩
  · -- injectivity
    rw [← sub_eq_zero]
    have hg' : ψ ≫ (g₁ - g₂) = 0 := by
      rw [comp_sub]
      exact sub_eq_zero.2 hg
    obtain ⟨h, hh⟩ := ye₃ (g₁ - g₂) (by rw [← hm₂, assoc, hg', comp_zero])
    have hβ (j : J) : ∃ β : (T j).obj₂⟦(1 : ℤ)⟧ ⟶ A,
        (ι₁ j)⟦(1 : ℤ)⟧' ≫ h = (T j).mor₁⟦(1 : ℤ)⟧' ≫ β := by
      have h0 : (T j).mor₃ ≫ (ι₁ j)⟦(1 : ℤ)⟧' ≫ h = 0 := by
        rw [← assoc, hc₃, assoc, ← hh, ← hι j, assoc, hg', comp_zero]
      obtain ⟨β, hβ⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ (hT j))
        ((ι₁ j)⟦(1 : ℤ)⟧' ≫ h) h0
      exact ⟨-β, by simpa using hβ⟩
    choose β hβ using hβ
    have hhβ : h = m₁⟦(1 : ℤ)⟧' ≫ Cofan.IsColimit.desc hc₂' β :=
      Cofan.IsColimit.hom_ext hc _ _ fun j ↦ by
        have e := Cofan.IsColimit.fac hc₂' β j
        simp only [Cofan.mk_pt, cofan_mk_inj] at e ⊢
        rw [hβ, ← Functor.map_comp_assoc, hι₁₂, Functor.map_comp_assoc, e]
    rw [hh, hhβ, ← assoc, z₃₁, zero_comp]
  · -- surjectivity
    have hz : m₁ ≫ m₂ ≫ a = 0 := by
      rw [← assoc]
      have : m₁ ≫ m₂ = 0 := Sigma.hom_ext _ _ fun j ↦ by
        rw [← assoc, hι₁₂, assoc, hι₂₃, ← assoc, comp_distTriang_mor_zero₁₂ _ (hT j),
          zero_comp, comp_zero]
      rw [this, zero_comp]
    obtain ⟨a', ha'⟩ := ye₂ (m₂ ≫ a) hz
    have hb (j : J) : ∃ b : (T j).obj₁⟦(1 : ℤ)⟧ ⟶ A,
        ι₃ j ≫ (a - ψ ≫ a') = (T j).mor₃ ≫ b := by
      have : m₂ ≫ (a - ψ ≫ a') = 0 := by
        rw [comp_sub, ← assoc, hm₂, sub_eq_zero]
        exact ha'
      have h' : (T j).mor₂ ≫ ι₃ j ≫ (a - ψ ≫ a') = 0 := by
        rw [← assoc, ← hι₂₃, assoc, this, comp_zero]
      exact Triangle.yoneda_exact₃ _ (hT j) _ h'
    choose b hb using hb
    refine ⟨a' + f₃ ≫ Cofan.IsColimit.desc hc b, ?_⟩
    have : m₃ ≫ Cofan.IsColimit.desc hc b = a - ψ ≫ a' :=
      Sigma.hom_ext _ _ fun j ↦ by
        have e := Cofan.IsColimit.fac hc b j
        simp only [Cofan.mk_pt, cofan_mk_inj] at e
        have := hι₃₁ j
        simp only [ι₃] at this hb
        rw [reassoc_of% this, e, hb]
    dsimp only
    rw [comp_add, ← assoc, ← hm₃, this, add_sub_cancel]

end Pretriangulated

end CategoryTheory
