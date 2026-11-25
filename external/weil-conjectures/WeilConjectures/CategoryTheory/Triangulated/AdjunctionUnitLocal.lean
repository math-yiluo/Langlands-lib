/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Objects local for an adjunction between pretriangulated categories

Let `L ⊣ R` be an adjunction between pretriangulated categories, compatible with the shifts, with
`L` and `R` triangulated (typically `L = j^*`, `R = Rj_*` for an open immersion `j`). An object
`X` is *local* when the unit `X ⟶ R L X` is an isomorphism. This file records the formal
properties of local objects used to compare the supported localization triangles along changes of
coefficients:

* `CategoryTheory.Adjunction.unitTriangleHom`: the unit as a morphism of triangles
  `T ⟶ (L ⋙ R).mapTriangle.obj T`;
* `CategoryTheory.Adjunction.isIso_unit_app_obj₃_of_distTriang`,
  `CategoryTheory.Adjunction.isIso_unit_app_obj₁_of_distTriang`: local objects satisfy the
  two-out-of-three property in distinguished triangles;
* `CategoryTheory.Adjunction.isIso_unit_app_iff_of_iso_obj`: locality is invariant under
  isomorphism;
* `CategoryTheory.Adjunction.isZero_of_isIso_unit_app`: a local object killed by `L` is zero;
* `CategoryTheory.Adjunction.isIso_unit_app_of_isIso_unit_app_map`: locality descends along a
  triangulated functor reflecting zero objects and commuting with the adjunctions.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Pretriangulated

namespace Adjunction

section Basic

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- Locality is invariant under isomorphism: the unit at `X` is invertible iff it is at `Y`. -/
lemma isIso_unit_app_iff_of_iso_obj {X Y : C} (e : X ≅ Y) :
    IsIso (adj.unit.app X) ↔ IsIso (adj.unit.app Y) := by
  have h := adj.unit.naturality e.hom
  dsimp at h
  constructor
  · intro
    have : IsIso (e.hom ≫ adj.unit.app Y) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  · intro
    have : IsIso (adj.unit.app X ≫ R.map (L.map e.hom)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (R.map (L.map e.hom))

/-- If the counit is invertible at `L X`, then `L` inverts the unit at `X`. -/
instance isIso_map_unit_app_of_isIso_counit_app (X : C) [IsIso (adj.counit.app (L.obj X))] :
    IsIso (L.map (adj.unit.app X)) := by
  have : IsIso (L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X)) := by
    rw [adj.left_triangle_components X]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adj.counit.app _)

/-- If the counit is an isomorphism, `L` inverts the unit. -/
lemma isIso_map_unit_app_of_isIso_counit [IsIso adj.counit] (X : C) :
    IsIso (L.map (adj.unit.app X)) :=
  adj.isIso_map_unit_app_of_isIso_counit_app X

/-- A local object killed by `L` is zero. -/
lemma isZero_of_isIso_unit_app [HasZeroMorphisms C] [HasZeroMorphisms D]
    [R.PreservesZeroMorphisms] {X : C} (h : IsIso (adj.unit.app X)) (hX : IsZero (L.obj X)) :
    IsZero X :=
  (R.map_isZero hX).of_iso (asIso (adj.unit.app X))

end Basic

section Shift

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ] [R.CommShift ℤ] [adj.CommShift ℤ]

/-- The unit of an adjunction `L ⊣ R` compatible with the shifts, as a morphism from a triangle
`T` to its image under `L ⋙ R`. -/
noncomputable def unitTriangleHom (T : Triangle C) : T ⟶ (L ⋙ R).mapTriangle.obj T :=
  Triangle.homMk _ _ (adj.unit.app T.obj₁) (adj.unit.app T.obj₂) (adj.unit.app T.obj₃)
    (adj.unit.naturality T.mor₁) (adj.unit.naturality T.mor₂) (by
      have h := adj.unit_app_commShiftIso_hom_app ℤ (1 : ℤ) T.obj₁
      have h' := adj.unit.naturality T.mor₃
      dsimp at h h' ⊢
      rw [← h, reassoc_of% h'])

@[simp]
lemma unitTriangleHom_hom₁ (T : Triangle C) :
    (adj.unitTriangleHom T).hom₁ = adj.unit.app T.obj₁ := rfl

@[simp]
lemma unitTriangleHom_hom₂ (T : Triangle C) :
    (adj.unitTriangleHom T).hom₂ = adj.unit.app T.obj₂ := rfl

@[simp]
lemma unitTriangleHom_hom₃ (T : Triangle C) :
    (adj.unitTriangleHom T).hom₃ = adj.unit.app T.obj₃ := rfl

end Shift

section

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ] [R.CommShift ℤ]
  [adj.CommShift ℤ] [L.IsTriangulated] [R.IsTriangulated]

/-- **Two out of three for local objects**, third vertex: if the units at the first two vertices
of a distinguished triangle are isomorphisms, so is the unit at the third vertex. -/
lemma isIso_unit_app_obj₃_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsIso (adj.unit.app T.obj₁)) (h₂ : IsIso (adj.unit.app T.obj₂)) :
    IsIso (adj.unit.app T.obj₃) :=
  isIso₃_of_isIso₁₂ (adj.unitTriangleHom T) hT ((L ⋙ R).map_distinguished T hT) h₁ h₂

/-- **Two out of three for local objects**, first vertex: if the units at the last two vertices
of a distinguished triangle are isomorphisms, so is the unit at the first vertex. -/
lemma isIso_unit_app_obj₁_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : IsIso (adj.unit.app T.obj₂)) (h₃ : IsIso (adj.unit.app T.obj₃)) :
    IsIso (adj.unit.app T.obj₁) :=
  isIso₁_of_isIso₂₃ (adj.unitTriangleHom T) hT ((L ⋙ R).map_distinguished T hT) h₂ h₃

/-- **Descent of locality.** Let `L ⊣ R` and `L' ⊣ R'` be adjunctions between pretriangulated
categories compatible with the shifts, with triangulated functors and invertible counits, and let
`F : C' ⥤ C` be a triangulated functor reflecting zero objects, such that `F (R' M) ≅ R (F' M)`
naturally and `L (F X) = 0` whenever `L' X = 0`. If `F N` is local for `L ⊣ R`, then `N` is local
for `L' ⊣ R'`.

The fibre `G` of the unit `N ⟶ R' L' N` is killed by `L'`; its image `F G` is the fibre of
`F N ⟶ F (R' L' N) ≅ R (F' L' N)`, a morphism between local objects, so `F G` is local and
killed by `L`, hence zero; so `G` is zero and the unit is invertible. -/
theorem isIso_unit_app_of_isIso_unit_app_map
    {C' D' : Type*} [Category* C'] [Category* D']
    [Preadditive C'] [HasZeroObject C'] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C' n).Additive]
    [Pretriangulated C']
    [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D']
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R') [L'.CommShift ℤ] [L'.IsTriangulated]
    [IsIso adj.counit] [IsIso adj'.counit]
    (F : C' ⥤ C) [F.CommShift ℤ] [F.IsTriangulated] (F' : D' ⥤ D)
    (e : R' ⋙ F ≅ F' ⋙ R) (hF : ∀ X, IsZero (F.obj X) → IsZero X)
    (hL : ∀ X, IsZero (L'.obj X) → IsZero (L.obj (F.obj X)))
    (N : C') (hN : IsIso (adj.unit.app (F.obj N))) : IsIso (adj'.unit.app N) := by
  obtain ⟨G, a, δ, hT⟩ := distinguished_cocone_triangle₁ (adj'.unit.app N)
  have hLG : IsZero (L'.obj G) :=
    (Triangle.isZero₁_iff_isIso₂ _ (L'.map_distinguished _ hT)).2
      (adj'.isIso_map_unit_app_of_isIso_counit N)
  have hFT := F.map_distinguished _ hT
  have h₃ : IsIso (adj.unit.app (F.obj (R'.obj (L'.obj N)))) :=
    (adj.isIso_unit_app_iff_of_iso_obj (e.app (L'.obj N))).2
      (adj.isIso_unit_app_obj_of_isIso_counit_app _)
  have h₁ := adj.isIso_unit_app_obj₁_of_distTriang _ hFT hN h₃
  have hG : IsZero G := hF G (adj.isZero_of_isIso_unit_app h₁ (hL G hLG))
  exact (Triangle.isZero₁_iff_isIso₂ _ hT).1 hG

end

end Adjunction

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Let `T` be a distinguished triangle and `A` an object with `Hom(A, T.obj₃) = 0` and
`Hom(A, T.obj₃⟦-1⟧) = 0`. Then composition with `T.mor₁` is a bijection
`Hom(A, T.obj₁) ≃ Hom(A, T.obj₂)`. -/
lemma bijective_comp_mor₁_of_subsingleton_shift {T : Triangle C} (hT : T ∈ distTriang C) (A : C)
    (h₃ : Subsingleton (A ⟶ T.obj₃)) (h₃' : Subsingleton (A ⟶ T.obj₃⟦(-1 : ℤ)⟧)) :
    Function.Bijective (fun x : A ⟶ T.obj₁ ↦ x ≫ T.mor₁) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) (x - y)
      (by simpa [Preadditive.sub_comp, sub_eq_zero] using hxy)
    rw [hg, h₃'.elim g 0, zero_comp]
  · obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ T hT y (Subsingleton.elim _ _)
    exact ⟨x, hx.symm⟩

end Pretriangulated

end CategoryTheory
