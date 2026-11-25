/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors and direct summands of finite sums

An additive functor preserves the property that an object is a direct summand of a finite direct
sum of copies of another object. The quasi-inverse of an additive equivalence is additive
(`CategoryTheory.Functor.additive_inv`). For an additive functor `G`, the image of a morphism
out of a finite biproduct is an isomorphism if and only if the morphism out of the biproduct of
the images is one (`CategoryTheory.Functor.isIso_map_biproductDesc`).
An additive functor carries an identity between sums of composites to the corresponding identity
between their images (`CategoryTheory.Functor.sum_const_map_comp_map_eq_sum`).
-/

@[expose] public section

open CategoryTheory

/-- An additive functor `F` preserves the property that `A` is a direct summand of a finite
direct sum of copies of `B`, up to isomorphisms `F A ≅ A'` and `F B ≅ B'`. -/
lemma CategoryTheory.Functor.exists_sum_comp_eq_id_of_iso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {A B : C} {A' B' : D}
    (eA : F.obj A ≅ A') (eB : F.obj B ≅ B')
    (h : ∃ (n : ℕ) (ξ : Fin n → (A ⟶ B)) (m : Fin n → (B ⟶ A)), ∑ j, ξ j ≫ m j = 𝟙 A) :
    ∃ (n : ℕ) (ξ : Fin n → (A' ⟶ B')) (m : Fin n → (B' ⟶ A')), ∑ j, ξ j ≫ m j = 𝟙 A' := by
  obtain ⟨n, ξ, m, h⟩ := h
  refine ⟨n, fun j ↦ eA.inv ≫ F.map (ξ j) ≫ eB.hom, fun j ↦ eB.inv ≫ F.map (m j) ≫ eA.hom, ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Preadditive.comp_sum]
  simp only [← Category.assoc, ← Preadditive.sum_comp]
  simp only [Category.assoc, ← F.map_comp, ← F.map_sum, h, F.map_id, Category.id_comp,
    Iso.inv_hom_id]


namespace CategoryTheory.Functor

open Limits

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor preserves biproducts indexed by a finite type in any universe. Compare
`CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive`, which is about index types in
`Type`. -/
instance (priority := 100) preservesBiproductsOfShape_of_additive {J : Type w} [Finite J]
    [Additive F] : PreservesBiproductsOfShape J F :=
  let ⟨_⟩ := nonempty_fintype J
  { preserves :=
    { preserves := fun hb =>
        ⟨isBilimitOfTotal _ (by
          simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
          erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩ } }

/-- The quasi-inverse of an additive equivalence of preadditive categories is additive. -/
instance additive_inv [F.IsEquivalence] [F.Additive] : F.inv.Additive :=
  have : F.asEquivalence.functor.Additive := ‹F.Additive›
  F.asEquivalence.inverse_additive

end CategoryTheory.Functor

namespace CategoryTheory

open Limits

section Biproduct

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] {ι : Type} [Finite ι]

/-- An additive functor carries a morphism `⨁ X ⟶ Y` out of a finite biproduct of copies of `X`
which is an isomorphism to a morphism out of a biproduct which is an isomorphism. -/
lemma Functor.isIso_biproductDesc_map (F : C ⥤ D) [F.Additive] {X Y : C} (φ : ι → (X ⟶ Y))
    [HasFiniteBiproducts D] [IsIso (biproduct.desc φ)] :
    IsIso (biproduct.desc fun i ↦ F.map (φ i)) := by
  have hc : biproduct.desc (fun i ↦ F.map (biproduct.ι (fun _ : ι ↦ X) i)) =
      (F.mapBiproduct fun _ : ι ↦ X).inv := by
    ext i
    simp [Functor.mapBiproduct]
  have h : (biproduct.desc fun i ↦ F.map (φ i)) =
      biproduct.desc (fun i ↦ F.map (biproduct.ι (fun _ : ι ↦ X) i)) ≫
        F.map (biproduct.desc φ) := by
    ext i
    simp [← F.map_comp]
  rw [h, hc]
  infer_instance


/-- The property that a morphism `⨁ X ⟶ Y` out of a biproduct of copies of `X`, given by maps
`φ i : X ⟶ Y`, is an isomorphism is invariant under isomorphisms of `X` and `Y` compatible with
the maps. -/
lemma isIso_biproductDesc_of_iso {X Y X' Y' : C} (φ : ι → (X ⟶ Y)) (φ' : ι → (X' ⟶ Y'))
    (e : X ≅ X') (e' : Y ≅ Y') (h : ∀ i, φ i ≫ e'.hom = e.hom ≫ φ' i)
    (h' : IsIso (biproduct.desc φ')) : IsIso (biproduct.desc φ) := by
  have hφ : biproduct.desc φ = biproduct.map (fun _ ↦ e.hom) ≫ biproduct.desc φ' ≫ e'.inv := by
    ext i
    simp [← reassoc_of% h i]
  have : IsIso (biproduct.map fun _ : ι ↦ e.hom) := (biproduct.mapIso fun _ ↦ e).isIso_hom
  rw [hφ]
  infer_instance

end Biproduct

end CategoryTheory

open Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] (G : C ⥤ D)
  [G.Additive] {J : Type} [Finite J] {f : J → C} [HasBiproduct f] {Y : C} (g : ∀ j, f j ⟶ Y)

/-- For an additive functor `G`, the image `G (⨁ f) ⟶ G Y` of the morphism out of a biproduct
with components `g j` is an isomorphism if and only if the morphism `⨁ G (f j) ⟶ G Y` with
components `G (g j)` is. -/
lemma isIso_map_biproductDesc :
    IsIso (G.map (biproduct.desc g)) ↔ IsIso (biproduct.desc fun j ↦ G.map (g j)) := by
  have := Fintype.ofFinite J
  have h : (biproduct.desc fun j ↦ G.map (g j)) =
      (G.mapBiproduct f).inv ≫ G.map (biproduct.desc g) :=
    biproduct.hom_ext' _ _ fun j ↦ by simp [← G.map_comp]
  rw [h, isIso_comp_left_iff]

end CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- The image under an additive functor of an identity `∑ _a, i ≫ E = ∑ a, i ≫ U a`. -/
lemma sum_const_map_comp_map_eq_sum {C D : Type*} [Category C] [Preadditive C] [Category D]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {P Q R : C} {κ : Type*} [Fintype κ] (i : P ⟶ Q)
    (E : Q ⟶ R) (U : κ → (Q ⟶ R)) (h : ∑ _a : κ, i ≫ E = ∑ a, i ≫ U a) :
    ∑ _a : κ, F.map i ≫ F.map E = ∑ a, F.map i ≫ F.map (U a) := by
  simp only [← F.map_comp, ← F.map_sum, h]

end CategoryTheory.Functor
