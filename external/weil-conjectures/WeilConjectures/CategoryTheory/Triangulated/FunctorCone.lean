/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Lifting a distinguished triangle along a triangulated functor

Let `F : C ⥤ D` be a functor between pretriangulated categories which is isomorphic to a
triangulated functor, and let `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` be a distinguished triangle in `D`. If
`T₃ ≅ F X₃`, `T₁⟦1⟧ ≅ F (X₁⟦1⟧)` and the connecting morphism `T₃ ⟶ T₁⟦1⟧` is, up to these
isomorphisms, `F δ` for some `δ : X₃ ⟶ X₁⟦1⟧`, then the cone `X₂` of `δ⟦-1⟧` satisfies
`F X₂ ≅ T₂` (`CategoryTheory.Functor.exists_distinguished_iso_obj₂_of_iso`), by TR3 and the
five lemma for triangles.

Auxiliary: `CategoryTheory.Functor.commShiftObjIsoOfIso` transports the commutation with shifts
along an isomorphism of functors.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category Limits Pretriangulated

/-- For an isomorphism `F ≅ G` with `G` commuting with the shifts, the isomorphism
`F (X⟦a⟧) ≅ (F X)⟦a⟧` transported from `G.commShiftIso a`. -/
noncomputable def commShiftObjIsoOfIso {A : Type*} [AddMonoid A] {C D : Type*} [Category* C]
    [Category* D] [HasShift C A] [HasShift D A] {F G : C ⥤ D} [G.CommShift A] (e : F ≅ G)
    (a : A) (X : C) : F.obj (X⟦a⟧) ≅ (F.obj X)⟦a⟧ :=
  e.app _ ≪≫ (G.commShiftIso a).app X ≪≫ (shiftFunctor D a).mapIso (e.app X).symm

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- Let `F ≅ G` with `G : C ⥤ D` triangulated, `T` a distinguished triangle in `D` and
`δ : X₃ ⟶ X₁⟦1⟧` a morphism in `C` such that `F δ` is the connecting morphism `T₃ ⟶ T₁⟦1⟧` up to
isomorphisms `F X₃ ≅ T₃` and `T₁⟦1⟧ ≅ F (X₁⟦1⟧)`. Then `δ` is the third morphism of a
distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` with `F X₂ ≅ T₂`. The hypothesis `h` is the
commutativity of
```
  F X₃ ──F δ──▶ F (X₁⟦1⟧)
   │ e₃            ▲ θ
   ▼               │
   T₃ ───T.mor₃──▶ T₁⟦1⟧
``` -/
lemma exists_distinguished_iso_obj₂_of_iso {F G : C ⥤ D} [G.CommShift ℤ] [G.IsTriangulated]
    (e : F ≅ G) (T : Triangle D) (hT : T ∈ distTriang D) {X₁ X₃ : C} (δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
    (e₃ : F.obj X₃ ≅ T.obj₃) (θ : T.obj₁⟦(1 : ℤ)⟧ ≅ F.obj (X₁⟦(1 : ℤ)⟧))
    (h : F.map δ = e₃.hom ≫ T.mor₃ ≫ θ.hom) :
    ∃ (X₂ : C) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃), Triangle.mk f g δ ∈ distTriang C ∧
      Nonempty (F.obj X₂ ≅ T.obj₂) := by
  obtain ⟨X₂, f, g, hfg⟩ := distinguished_cocone_triangle₂ δ
  let ψ : T.obj₁⟦(1 : ℤ)⟧ ≅ (G.obj X₁)⟦(1 : ℤ)⟧ :=
    θ ≪≫ e.app _ ≪≫ (G.commShiftIso (1 : ℤ)).app X₁
  let a : T.obj₁ ≅ G.obj X₁ := (shiftFunctor D (1 : ℤ)).preimageIso ψ
  let c : T.obj₃ ≅ G.obj X₃ := e₃.symm ≪≫ e.app X₃
  have comm : T.mor₃ ≫ a.hom⟦(1 : ℤ)⟧' =
      c.hom ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app X₁ := by
    have h' := e.hom.naturality δ
    simp only [a, c, ψ, preimageIso_hom, map_preimage, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, assoc]
    rw [← reassoc_of% h', h]
    simp
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hT
    (G.map_distinguished _ hfg) a.hom c.hom comm
  let φ : T ⟶ G.mapTriangle.obj (Triangle.mk f g δ) :=
    Triangle.homMk _ _ a.hom b c.hom hb₁ hb₂ comm
  have : IsIso φ.hom₂ := isIso₂_of_isIso₁₃ φ hT (G.map_distinguished _ hfg)
    (inferInstanceAs (IsIso a.hom)) (inferInstanceAs (IsIso c.hom))
  exact ⟨X₂, f, g, hfg, ⟨e.app X₂ ≪≫ (asIso φ.hom₂).symm⟩⟩

end CategoryTheory.Functor
