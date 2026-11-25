/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Extensions of essentially small properties of objects

Let `C` be a pretriangulated category which is locally `w`-small. If `P` and `Q` are essentially
`w`-small properties of objects, then so is their extension product `P.extensionProduct Q`
(`CategoryTheory.ObjectProperty.essentiallySmall_extensionProduct`): an extension
`Y ⟶ X ⟶ Z ⟶ Y⟦1⟧` is determined up to isomorphism by the connecting morphism `Z ⟶ Y⟦1⟧`, and
these form a set once `Y` and `Z` range over small sets of representatives.

We also record when a homological functor sends `T.mor₁` or `T.mor₂` of a distinguished
triangle `T` to an isomorphism (`CategoryTheory.Functor.isIso_shift_map_mor₁_of_isZero`,
`CategoryTheory.Functor.isIso_shift_map_mor₂_of_isZero`).
-/

@[expose] public section

universe w v u u'

open CategoryTheory Limits Pretriangulated Category

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace ObjectProperty

/-- The extension product of two essentially small properties of objects of a locally small
pretriangulated category is essentially small. -/
instance essentiallySmall_extensionProduct [LocallySmall.{w} C] (P Q : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q] :
    ObjectProperty.EssentiallySmall.{w} (P.extensionProduct Q) := by
  obtain ⟨P₀, _, hP₀⟩ := EssentiallySmall.exists_small_le' P
  obtain ⟨Q₀, _, hQ₀⟩ := EssentiallySmall.exists_small_le' Q
  have h (x : Σ (y : Subtype P₀) (z : Subtype Q₀), Shrink.{w} (z.1 ⟶ y.1⟦(1 : ℤ)⟧)) :=
    distinguished_cocone_triangle₂ ((equivShrink _).symm x.2.2)
  choose W f g hT using h
  refine ⟨ofObj W, inferInstance, fun X ⟨Y, Z, f', g', h', hT', hY, hZ⟩ ↦ ?_⟩
  obtain ⟨y, hy, ⟨e₁⟩⟩ := hP₀ Y hY
  obtain ⟨z, hz, ⟨e₃⟩⟩ := hQ₀ Z hZ
  let x : Σ (y : Subtype P₀) (z : Subtype Q₀), Shrink.{w} (z.1 ⟶ y.1⟦(1 : ℤ)⟧) :=
    ⟨⟨y, hy⟩, ⟨z, hz⟩, equivShrink _ (e₃.inv ≫ h' ≫ e₁.hom⟦(1 : ℤ)⟧')⟩
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hT' (hT x) e₁.hom e₃.hom
    (by simp [x])
  let φ : Triangle.mk f' g' h' ⟶ Triangle.mk (f x) (g x) ((equivShrink _).symm x.2.2) :=
    { hom₁ := e₁.hom
      hom₂ := b
      hom₃ := e₃.hom
      comm₁ := hb₁
      comm₂ := hb₂
      comm₃ := by simp [x] }
  have : IsIso φ.hom₂ := isIso₂_of_isIso₁₃ φ hT' (hT x) inferInstance inferInstance
  exact ⟨W x, ofObj_apply _ _, ⟨asIso φ.hom₂⟩⟩

end ObjectProperty

namespace Functor

variable {A : Type u'} [Category A] [Abelian A] (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
  (T : Triangle C) (hT : T ∈ distTriang C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
include hT h

/-- A homological functor sends `T.mor₁` of a distinguished triangle `T` to an isomorphism in
degree `n₁ = n₀ + 1` if it vanishes on `T.obj₃` in degrees `n₀` and `n₁`. -/
lemma isIso_shift_map_mor₁_of_isZero (h₀ : IsZero ((F.shift n₀).obj T.obj₃))
    (h₁ : IsZero ((F.shift n₁).obj T.obj₃)) : IsIso ((F.shift n₁).map T.mor₁) := by
  have : Mono ((F.shift n₁).map T.mor₁) :=
    (F.homologySequence_mono_shift_map_mor₁_iff T hT n₀ n₁ h).2 (h₀.eq_of_src _ _)
  have : Epi ((F.shift n₁).map T.mor₁) :=
    (F.homologySequence_epi_shift_map_mor₁_iff T hT n₁).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- A homological functor sends `T.mor₂` of a distinguished triangle `T` to an isomorphism in
degree `n₀` if it vanishes on `T.obj₁` in degrees `n₀` and `n₁ = n₀ + 1`. -/
lemma isIso_shift_map_mor₂_of_isZero (h₀ : IsZero ((F.shift n₀).obj T.obj₁))
    (h₁ : IsZero ((F.shift n₁).obj T.obj₁)) : IsIso ((F.shift n₀).map T.mor₂) := by
  have : Mono ((F.shift n₀).map T.mor₂) :=
    (F.homologySequence_mono_shift_map_mor₂_iff T hT n₀).2 (h₀.eq_of_src _ _)
  have : Epi ((F.shift n₀).map T.mor₂) :=
    (F.homologySequence_epi_shift_map_mor₂_iff T hT n₀ n₁ h).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Functor

end CategoryTheory
