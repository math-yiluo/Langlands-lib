/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.HomologicalBicomplex

/-!
# The Čech double complex of an injective resolution

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 1 (blueprint:
def-sc-cech-resolution-double-complex).
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

section
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {ι : Type v} (U : ι → C)

instance : (cechComplexFunctor (A := AddCommGrpCat.{v}) U).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    apply HomologicalComplex.hom_ext
    intro n
    dsimp [cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor,
      AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Limits.FormalCoproduct.evalOp]
    apply Pi.hom_ext
    intro i
    simp

end

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]

/-- Apply the Čech functor termwise to an injective resolution, then exchange the
resolution and Čech indices. Thus the outer index is the Čech degree and the inner
index is the resolution degree. Functoriality gives commuting differentials.
Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 1.
(blueprint: def-sc-cech-resolution-double-complex) -/
noncomputable def Sheaf.cechResolutionDoubleComplex
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) :
    HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.flip (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op ⋙
    cechComplexFunctor (fun i ↦ Over.mk (π i))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)

end CategoryTheory
