/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Morphisms of triangles induced by natural transformations

A natural transformation `τ : F₁ ⟶ F₂` between functors commuting with the shifts by `ℤ`
which is itself compatible with the shifts induces a natural transformation
`F₁.mapTriangle ⟶ F₂.mapTriangle` (`CategoryTheory.NatTrans.mapTriangle`): its component at a
triangle `T` is the morphism of triangles with components `τ.app T.obj₁`, `τ.app T.obj₂` and
`τ.app T.obj₃`. This is the counterpart for morphisms of Mathlib's
`CategoryTheory.Functor.mapTriangleIso`.

When `F₁` and `F₂` are triangulated, we deduce that if `τ` is an isomorphism on two terms of a
distinguished triangle, then it is an isomorphism on the third
(`CategoryTheory.NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂` and its variants).
-/

@[expose] public section

namespace CategoryTheory.NatTrans

open Category Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation `τ : F₁ ⟶ F₂` compatible with the shifts induces a natural
transformation `F₁.mapTriangle ⟶ F₂.mapTriangle`, whose components are the morphisms of
triangles with components `τ.app T.obj₁`, `τ.app T.obj₂` and `τ.app T.obj₃`. -/
@[simps!]
def mapTriangle (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] : F₁.mapTriangle ⟶ F₂.mapTriangle where
  app T := Triangle.homMk _ _ (τ.app _) (τ.app _) (τ.app _) (by simp) (by simp) (by
    dsimp
    simp only [assoc, NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁, NatTrans.naturality_assoc])
  naturality T T' f := by
    apply Triangle.hom_ext <;> simp

section TwoOutOfThree

open Limits

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [F₁.IsTriangulated] [F₂.IsTriangulated]
  (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] {T : Triangle C} (hT : T ∈ distTriang C)

include hT

/-- Blueprint `lemma-checking-isomorphisms-constructible-complexes--1`: a natural transformation
between triangulated functors, compatible with the shifts, which is an isomorphism on the first two
terms of a distinguished triangle is an isomorphism on the third. -/
lemma isIso_app_obj₃_of_isIso_app_obj₁₂ (h₁ : IsIso (τ.app T.obj₁)) (h₂ : IsIso (τ.app T.obj₂)) :
    IsIso (τ.app T.obj₃) :=
  isIso₃_of_isIso₁₂ ((mapTriangle τ).app T) (F₁.map_distinguished T hT)
    (F₂.map_distinguished T hT) h₁ h₂

/-- Blueprint `lemma-checking-isomorphisms-constructible-complexes--1`: a natural transformation
between triangulated functors, compatible with the shifts, which is an isomorphism on the first and
third terms of a distinguished triangle is an isomorphism on the second. -/
lemma isIso_app_obj₂_of_isIso_app_obj₁₃ (h₁ : IsIso (τ.app T.obj₁)) (h₃ : IsIso (τ.app T.obj₃)) :
    IsIso (τ.app T.obj₂) :=
  isIso₂_of_isIso₁₃ ((mapTriangle τ).app T) (F₁.map_distinguished T hT)
    (F₂.map_distinguished T hT) h₁ h₃

/-- Blueprint `lemma-checking-isomorphisms-constructible-complexes--1`: a natural transformation
between triangulated functors, compatible with the shifts, which is an isomorphism on the last two
terms of a distinguished triangle is an isomorphism on the first. -/
lemma isIso_app_obj₁_of_isIso_app_obj₂₃ (h₂ : IsIso (τ.app T.obj₂)) (h₃ : IsIso (τ.app T.obj₃)) :
    IsIso (τ.app T.obj₁) :=
  isIso₁_of_isIso₂₃ ((mapTriangle τ).app T) (F₁.map_distinguished T hT)
    (F₂.map_distinguished T hT) h₂ h₃

end TwoOutOfThree

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- **Exact functors of pre-triangulated categories.** A functor `F` equipped with a
commutation with the shifts (`F.CommShift ℤ`) is exact (triangulated) if and only if it carries
distinguished triangles to distinguished triangles. (blueprint: `def-weil-triangulated-category`)
-/
theorem isTriangulated_iff_map_distinguished (F : C ⥤ D) [F.CommShift ℤ] :
    F.IsTriangulated ↔ ∀ T ∈ distTriang C, F.mapTriangle.obj T ∈ distTriang D :=
  ⟨fun h ↦ h.map_distinguished, fun h ↦ ⟨h⟩⟩

end CategoryTheory.Functor
