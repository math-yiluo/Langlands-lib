/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
import all WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones

/-! # Transport of strict tensor cone towers
Source: Stacks 06YP (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

private def coneTowerMap
    {B : Type*} [Category B] [Abelian B]
    {X Y X' Y' : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    levelConeTower f ⟶ levelConeTower g where
  app n := CochainComplex.mappingCone.map (f.app n) (g.app n)
    (a.app n) (b.app n) (congr_app h n)
  naturality m n t := by
    dsimp only [levelConeTower]
    rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
    congr 1
    · exact a.naturality t
    · exact b.naturality t

private def coneTowerIso
    {B : Type*} [Category B] [Abelian B]
    {X Y X' Y' : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') (h : f ≫ b.hom = a.hom ≫ g) :
    levelConeTower f ≅ levelConeTower g where
  hom := coneTowerMap f g a.hom b.hom h
  inv := coneTowerMap g f a.inv b.inv (by
    apply (cancel_epi a.hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    dsimp only [coneTowerMap, NatTrans.comp_app, NatTrans.id_app]
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.hom_inv_id_app, CochainComplex.mappingCone.map_id]
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    dsimp only [coneTowerMap, NatTrans.comp_app, NatTrans.id_app]
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.inv_hom_id_app, CochainComplex.mappingCone.map_id]
    rfl

/-- A tensor square of strict towers induces an isomorphism of their cone towers.
Source: Stacks 06YP (auxiliary; not a blueprint node).
Proof: transpose to towers of complexes. The additive evaluation functors identify
transposition of a cone with its levelwise cone. The signed tensor-cone comparison
is natural in every transition. Apply the cone map to the given square and to
its inverse square, and compose the three tower isomorphisms. -/
theorem tensorConeTowerIso
    {B : Type*} [Category B] [Abelian B]
    (F : B ⥤ B ⥤ B) [F.Additive] [∀ X : B, (F.obj X).Additive]
    [∀ K L : CochainComplex B ℤ, HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
    (P : CochainComplex B ℤ)
    {X Y X' Y' : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X.asFunctor ⋙ (Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P ≅
      X'.asFunctor)
    (b : Y.asFunctor ⋙ (Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P ≅
      Y'.asFunctor)
    (h : Functor.whiskerRight
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)
        ((Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P) ≫ b.hom =
      a.hom ≫ HomologicalComplex.complexOfFunctorsToFunctorToComplex.map g) :
    Nonempty ((CochainComplex.mappingCone f).asFunctor ⋙
      (Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P ≅
        (CochainComplex.mappingCone g).asFunctor) := by
  let β := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f
  let γ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map g
  let T := (Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P
  exact ⟨Functor.isoWhiskerRight (levelConeTowerIso β) T ≪≫
    levelConeTower_mapBifunctorIso F P β ≪≫
    coneTowerIso (Functor.whiskerRight β T) γ a b h ≪≫ (levelConeTowerIso γ).symm⟩

end CategoryTheory.ConstantCompletion
