/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Finite matrix coordinates under additive functors
Source: blueprint Compatible isomorphisms, finite matrices and ordinary scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type u} {D : Type v} {E : Type w}
  [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts E]

omit [HasFiniteBiproducts D] [HasFiniteBiproducts E] in
/-- The biproduct comparison for a composite is the composite of the comparisons.
Source: finite matrix coordinates in Compatible isomorphisms.
(blueprint: lem-pe-functor-finite-matrix-coordinates).
Proof: postcompose both morphisms with each biproduct projection. Both become the
composite functor applied to that projection. -/
theorem mapBiproduct_composite (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    {I : Type} [Finite I] (f : I → C) :
    (F ⋙ G).mapBiproduct f =
      G.mapIso (F.mapBiproduct f) ≪≫ G.mapBiproduct (fun i ↦ F.obj (f i)) := by
  apply Iso.ext
  apply biproduct.hom_ext
  intro i
  simp only [mapBiproduct_hom, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Functor.comp_map]
  erw [biproduct.lift_π, biproduct.lift_π, ← G.map_comp, biproduct.lift_π]

omit [HasFiniteBiproducts D] in
/-- Biproduct comparisons are natural in each member of the finite family.
Source: finite matrix coordinates in Compatible isomorphisms.
(blueprint: lem-pe-functor-finite-matrix-coordinates).
Proof: postcompose with a projection, use the defining comparison formula and
naturality of biproduct.map, and combine the functor's two maps. -/
theorem mapBiproduct_map (F : C ⥤ D) [F.Additive]
    {I : Type} [Finite I] {f g : I → C} (a : ∀ i, f i ⟶ g i) :
    F.map (biproduct.map a) ≫ (F.mapBiproduct g).hom =
      (F.mapBiproduct f).hom ≫ biproduct.map (fun i ↦ F.map (a i)) := by
  apply biproduct.hom_ext
  intro i
  simp only [mapBiproduct_hom, Category.assoc]
  erw [biproduct.lift_π, biproduct.map_π, ← Category.assoc, biproduct.lift_π,
    ← F.map_comp, biproduct.map_π]
  exact F.map_comp _ _

/-- An additive functor maps a finite matrix entry by entry in its biproduct coordinates.
Source: finite matrix coordinates in Compatible isomorphisms.
(blueprint: lem-pe-functor-finite-matrix-coordinates).
Proof: precompose by the inverse source comparison, then test every inclusion and
projection. The comparison formulas reduce both sides to F applied to one entry. -/
theorem mapBiproduct_matrix (F : C ⥤ D) [F.Additive]
    {I J : Type} [Finite I] [Finite J] {f : I → C} {g : J → C}
    (a : ∀ i j, f i ⟶ g j) :
    F.map (biproduct.matrix a) ≫ (F.mapBiproduct g).hom =
      (F.mapBiproduct f).hom ≫ biproduct.matrix (fun i j ↦ F.map (a i j)) := by
  apply (cancel_epi (F.mapBiproduct f).inv).1
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  have hι : biproduct.ι (fun i ↦ F.obj (f i)) i ≫ (F.mapBiproduct f).inv =
      F.map (biproduct.ι f i) := by
    exact biproduct.ι_desc _ _
  have hπ : (F.mapBiproduct g).hom ≫ biproduct.π (fun j ↦ F.obj (g j)) j =
      F.map (biproduct.π g j) := by
    exact biproduct.lift_π _ _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Category.assoc (biproduct.ι _ i), hι,
    hπ, ← F.map_comp, ← F.map_comp]
  erw [biproduct.ι_matrix_assoc, biproduct.lift_π, biproduct.ι_matrix_assoc,
    biproduct.lift_π]

omit [HasFiniteBiproducts D] in
/-- Biproduct comparison is natural in an additive functor transformation.
Source: blueprint Compatible isomorphisms, comparing two scalar extensions.
(blueprint: lem-pe-functor-finite-matrix-coordinates).
Proof: after each target projection the identity is exactly naturality at the
corresponding source projection. -/
theorem mapBiproduct_natTrans (F G : C ⥤ D) [F.Additive] [G.Additive]
    (η : F ⟶ G) {I : Type} [Finite I] (f : I → C) :
    η.app (⨁ f) ≫ (G.mapBiproduct f).hom =
      (F.mapBiproduct f).hom ≫ biproduct.map (fun i ↦ η.app (f i)) := by
  apply biproduct.hom_ext
  intro i
  simp only [mapBiproduct_hom, Category.assoc]
  erw [biproduct.lift_π, biproduct.map_π, ← Category.assoc, biproduct.lift_π]
  exact (η.naturality (biproduct.π f i)).symm

/-- Finite diagonal maps respect composition.
Source: blueprint Compatible isomorphisms, composition of finite free comparisons.
(blueprint: lem-pe-functor-finite-matrix-coordinates).
Proof: after each target projection both sides are that projection followed by
the two corresponding component maps. -/
theorem biproduct_map_comp {I : Type} [Finite I] {f g h : I → C}
    (a : ∀ i, f i ⟶ g i) (b : ∀ i, g i ⟶ h i) :
    biproduct.map (fun i ↦ a i ≫ b i) = biproduct.map a ≫ biproduct.map b := by
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, biproduct.map_π]
  rw [← Category.assoc (biproduct.map a), biproduct.map_π, Category.assoc]

end CategoryTheory.Functor
