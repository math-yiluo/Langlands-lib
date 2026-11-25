/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Natural transformations and the long exact sequences of a homological functor

Let `H : D ⥤ A` be a homological functor equipped with a shift sequence, and let
`τ : F₁ ⟶ F₂` be a natural transformation between triangulated functors `C ⥤ D` which is
compatible with the shifts. For a distinguished triangle `T` in `C`, the images of `T` under
`F₁` and `F₂` are distinguished, and the maps `H^n(τ)` form a morphism between the two long
exact sequences of homology: they commute with the connecting morphisms
(`CategoryTheory.Functor.homologySequenceδ_mapTriangle_naturality`).

`CategoryTheory.Functor.exists_homologySequenceδ_whiskerRight` packages this for the triangle
`L(X₁) ⟶ L(X₂) ⟶ L(X₃) ⟶ L(X₁)[1]` attached to a short complex `X₁ ⟶ X₂ ⟶ X₃` by a functor
`L`, in terms of the functors `L ⋙ F₁ ⋙ H^n` and `L ⋙ F₂ ⋙ H^n` and the natural
transformations between them induced by `τ`. These functors and transformations are taken as
arbitrary data with an equation identifying them, so that the statement applies to concrete
functors which are only definitionally of this form, without the kernel having to unfold
them.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits Pretriangulated

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Abelian A]
  (H : D ⥤ A) [H.ShiftSequence ℤ]

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Abelian A] in
/-- For a natural transformation `τ : F₁ ⟶ F₂` compatible with the shifts and a triangle `T`,
the maps `H^n(τ)` commute with the connecting morphisms of the homology sequences of the
triangles `F₁(T)` and `F₂(T)`. -/
lemma homologySequenceδ_mapTriangle_naturality {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ]
    [F₂.CommShift ℤ] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    H.homologySequenceδ (F₁.mapTriangle.obj T) n₀ n₁ h ≫ (H.shift n₁).map (τ.app T.obj₁) =
      (H.shift n₀).map (τ.app T.obj₃) ≫ H.homologySequenceδ (F₂.mapTriangle.obj T) n₀ n₁ h :=
  (H.homologySequenceδ_naturality ((NatTrans.mapTriangle τ).app T) n₀ n₁ h).symm

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [H.IsHomological]

/-- Let `L : C₀ ⥤ C` be a functor, `X₁ ⟶ X₂ ⟶ X₃` a short complex in `C₀` whose image under
`L` extends to a distinguished triangle, and `τ : F₁ ⟶ F₂` a natural transformation between
triangulated functors `C ⥤ D` compatible with the shifts. Let `Gᵢ n` be the functor
`L ⋙ Fᵢ ⋙ H.shift n` and `φ n : G₁ n ⟶ G₂ n` the natural transformation induced by `τ`. Then
there are connecting morphisms `δᵢ : (Gᵢ n₀).obj X₃ ⟶ (Gᵢ n₁).obj X₁`, where `n₀ + 1 = n₁`,
making the sequences `(Gᵢ n₀).obj X₂ ⟶ (Gᵢ n₀).obj X₃ ⟶ (Gᵢ n₁).obj X₁ ⟶ (Gᵢ n₁).obj X₂`
exact, and commuting with the maps `φ n₀` and `φ n₁`.

The functors `H.shift n`, `Gᵢ n` and the transformations `φ n` are taken as arbitrary data
together with equations identifying them, so that the statement can be applied to concrete
functors which are only definitionally of this form. -/
theorem exists_homologySequenceδ_whiskerRight {C₀ : Type*} [Category* C₀]
    [HasZeroMorphisms C₀] (L : C₀ ⥤ C) {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    [F₁.IsTriangulated] [F₂.IsTriangulated] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ]
    (Hn : ℤ → D ⥤ A) (hH : ∀ n, H.shift n = Hn n) (G₁ G₂ : ℤ → C₀ ⥤ A)
    (φ : ∀ n, G₁ n ⟶ G₂ n)
    (hφ : (⟨G₁, G₂, φ⟩ : Σ (G₁ G₂ : ℤ → C₀ ⥤ A), ∀ n, G₁ n ⟶ G₂ n) =
      ⟨fun n ↦ L ⋙ F₁ ⋙ Hn n, fun n ↦ L ⋙ F₂ ⋙ Hn n,
        fun n ↦ whiskerLeft L (whiskerRight τ (Hn n))⟩)
    (E : ShortComplex C₀) (δ : L.obj E.X₃ ⟶ (L.obj E.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (L.map E.f) (L.map E.g) δ ∈ distTriang C) (n₀ n₁ : ℤ)
    (hn : n₀ + 1 = n₁) :
    ∃ (δ₁ : (G₁ n₀).obj E.X₃ ⟶ (G₁ n₁).obj E.X₁) (δ₂ : (G₂ n₀).obj E.X₃ ⟶ (G₂ n₁).obj E.X₁)
      (w₁ : (G₁ n₀).map E.g ≫ δ₁ = 0) (w₂ : δ₁ ≫ (G₁ n₁).map E.f = 0)
      (w₃ : (G₂ n₀).map E.g ≫ δ₂ = 0) (w₄ : δ₂ ≫ (G₂ n₁).map E.f = 0),
      (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact ∧
      (ShortComplex.mk _ _ w₃).Exact ∧ (ShortComplex.mk _ _ w₄).Exact ∧
      δ₁ ≫ (φ n₁).app E.X₁ = (φ n₀).app E.X₃ ≫ δ₂ := by
  obtain rfl : (fun n ↦ H.shift n) = Hn := funext hH
  cases hφ
  let T := Triangle.mk (L.map E.f) (L.map E.g) δ
  have h₁ : F₁.mapTriangle.obj T ∈ distTriang D := F₁.map_distinguished _ hT
  have h₂ : F₂.mapTriangle.obj T ∈ distTriang D := F₂.map_distinguished _ hT
  exact ⟨H.homologySequenceδ (F₁.mapTriangle.obj T) n₀ n₁ hn,
    H.homologySequenceδ (F₂.mapTriangle.obj T) n₀ n₁ hn,
    H.comp_homologySequenceδ _ h₁ n₀ n₁ hn, H.homologySequenceδ_comp _ h₁ n₀ n₁ hn,
    H.comp_homologySequenceδ _ h₂ n₀ n₁ hn, H.homologySequenceδ_comp _ h₂ n₀ n₁ hn,
    H.homologySequence_exact₃ _ h₁ n₀ n₁ hn, H.homologySequence_exact₁ _ h₁ n₀ n₁ hn,
    H.homologySequence_exact₃ _ h₂ n₀ n₁ hn, H.homologySequence_exact₁ _ h₂ n₀ n₁ hn,
    H.homologySequenceδ_mapTriangle_naturality τ T n₀ n₁ hn⟩

/-- The form of `CategoryTheory.Functor.exists_homologySequenceδ_whiskerRight` for an arbitrary
instance of zero morphisms on `A`, in which the exactness of the two long sequences is stated.
Use it when that instance is not the one of the abelian structure, for instance for sheaves,
whose zero morphisms come from the full subcategory of sheaves: there the kernel would have to
compare the two instances, which is expensive. -/
theorem exists_homologySequenceδ_whiskerRight' [ZA : HasZeroMorphisms A] {C₀ : Type*}
    [Category* C₀] [HasZeroMorphisms C₀] (L : C₀ ⥤ C) {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ]
    [F₂.CommShift ℤ] [F₁.IsTriangulated] [F₂.IsTriangulated] (τ : F₁ ⟶ F₂)
    [NatTrans.CommShift τ ℤ] (Hn : ℤ → D ⥤ A) (hH : ∀ n, H.shift n = Hn n)
    (G₁ G₂ : ℤ → C₀ ⥤ A) (φ : ∀ n, G₁ n ⟶ G₂ n)
    (hφ : (⟨G₁, G₂, φ⟩ : Σ (G₁ G₂ : ℤ → C₀ ⥤ A), ∀ n, G₁ n ⟶ G₂ n) =
      ⟨fun n ↦ L ⋙ F₁ ⋙ Hn n, fun n ↦ L ⋙ F₂ ⋙ Hn n,
        fun n ↦ whiskerLeft L (whiskerRight τ (Hn n))⟩)
    (E : ShortComplex C₀) (δ : L.obj E.X₃ ⟶ (L.obj E.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (L.map E.f) (L.map E.g) δ ∈ distTriang C) (n₀ n₁ : ℤ)
    (hn : n₀ + 1 = n₁) :
    ∃ (δ₁ : (G₁ n₀).obj E.X₃ ⟶ (G₁ n₁).obj E.X₁) (δ₂ : (G₂ n₀).obj E.X₃ ⟶ (G₂ n₁).obj E.X₁)
      (w₁ : (G₁ n₀).map E.g ≫ δ₁ = 0) (w₂ : δ₁ ≫ (G₁ n₁).map E.f = 0)
      (w₃ : (G₂ n₀).map E.g ≫ δ₂ = 0) (w₄ : δ₂ ≫ (G₂ n₁).map E.f = 0),
      (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact ∧
      (ShortComplex.mk _ _ w₃).Exact ∧ (ShortComplex.mk _ _ w₄).Exact ∧
      δ₁ ≫ (φ n₁).app E.X₁ = (φ n₀).app E.X₃ ≫ δ₂ := by
  obtain rfl : ZA = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  exact H.exists_homologySequenceδ_whiskerRight L τ Hn hH G₁ G₂ φ hφ E δ hT n₀ n₁ hn

end CategoryTheory.Functor
