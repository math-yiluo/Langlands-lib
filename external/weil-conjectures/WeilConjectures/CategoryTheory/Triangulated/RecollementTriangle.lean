/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!

# Recognizing the triangle of a recollement

Let `F₁ : C ⥤ D₁` and `F₂ : C ⥤ D₂` be triangulated functors between pretriangulated categories
which jointly reflect isomorphisms (for instance the restrictions `j^*` and `i^*` to an open
subscheme and its closed complement). Two composable morphisms `f : A ⟶ M` and `g : M ⟶ N` with
`f ≫ g = 0` such that `F₁ f` is an isomorphism and `F₁ N = 0`, while `F₂ A = 0` and `F₂ g` is an
isomorphism, extend to a distinguished triangle `A ⟶ M ⟶ N ⟶ A⟦1⟧`
(`CategoryTheory.Pretriangulated.exists_distTriang_of_jointlyReflectIsomorphisms`): the
cone of `f` maps to `N`, and this comparison is inverted by `F₁` and by `F₂`.

This is how the open–closed triangle `j_! j^* K ⟶ K ⟶ i_* i^* K ⟶` is obtained from the
counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Pretriangulated

universe v u

variable {C : Type*} [Category C] {D₁ D₂ : Type u} [Category.{v} D₁] [Category.{v} D₂]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [Preadditive D₁] [HasZeroObject D₁] [HasShift D₁ ℤ] [∀ n : ℤ, (shiftFunctor D₁ n).Additive]
  [Pretriangulated D₁]
  [Preadditive D₂] [HasZeroObject D₂] [HasShift D₂ ℤ] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [Pretriangulated D₂]
  {F₁ : C ⥤ D₁} {F₂ : C ⥤ D₂} [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₁.IsTriangulated]
  [F₂.IsTriangulated]

/-- **The triangle of a recollement.** Let `F₁` and `F₂` be triangulated functors jointly
reflecting isomorphisms, and `f : A ⟶ M`, `g : M ⟶ N` with `f ≫ g = 0`, such that `F₁ f` is an
isomorphism, `F₁ N = 0`, `F₂ A = 0` and `F₂ g` is an isomorphism. Then `f` and `g` extend to a
distinguished triangle `A ⟶ M ⟶ N ⟶ A⟦1⟧`.

Proof: complete `f` to a distinguished triangle `A ⟶ M ⟶ P ⟶ A⟦1⟧`. Since `f ≫ g = 0`, the map
`g` factors through `P` by a comparison `φ : P ⟶ N`:

```
  A ──f──▶ M ──g'──▶ P ──h──▶ A⟦1⟧
  ‖        ‖         │φ        ‖
  A ──f──▶ M ──g───▶ N ─────▶ A⟦1⟧
```

`F₁ φ` is a map between zero objects (`F₁ P = 0` as `F₁ f` is an isomorphism), and `F₂ φ` is an
isomorphism (`F₂ g'` is one as `F₂ A = 0`, and `F₂ g' ≫ F₂ φ = F₂ g`). So `φ` is an isomorphism,
and the bottom row, with `δ = φ⁻¹ ≫ h`, is distinguished. -/
lemma exists_distTriang_of_jointlyReflectIsomorphisms
    (hF : JointlyReflectIsomorphisms (pairFunctor F₁ F₂)) {A M N : C} (f : A ⟶ M) (g : M ⟶ N)
    (hfg : f ≫ g = 0) (h₁ : IsIso (F₁.map f)) (hN : IsZero (F₁.obj N))
    (hA : IsZero (F₂.obj A)) (h₂ : IsIso (F₂.map g)) :
    ∃ δ : N ⟶ A⟦(1 : ℤ)⟧, Triangle.mk f g δ ∈ distTriang C := by
  obtain ⟨P, g', h, hT⟩ := distinguished_cocone_triangle f
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₂ _ hT g hfg
  have hP : IsZero (F₁.obj P) :=
    (Triangle.isZero₃_iff_isIso₁ _ (F₁.map_distinguished _ hT)).2 h₁
  have hg' : IsIso (F₂.map g') :=
    (Triangle.isZero₁_iff_isIso₂ _ (F₂.map_distinguished _ hT)).1 hA
  have : IsIso (F₂.map g' ≫ F₂.map φ) := by
    rw [← F₂.map_comp]
    exact hφ ▸ h₂
  have : IsIso φ := hF.isIso_of_pairFunctor φ
    (isIso_of_source_target_iso_zero _ hP.isoZero hN.isoZero)
    (IsIso.of_isIso_comp_left (F₂.map g') _)
  refine ⟨inv φ ≫ h, isomorphic_distinguished _ hT _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso φ).symm (by simp)
    (by simp [hφ]) (by simp)

end CategoryTheory.Pretriangulated
