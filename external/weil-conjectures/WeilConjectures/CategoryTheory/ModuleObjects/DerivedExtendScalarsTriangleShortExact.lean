/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleNatural

/-!

# The connecting morphism of the reduction triangle on a complex with short exact reduction

Let `φ : R ⟶ S` be a morphism of commutative algebra objects such that
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact. The natural connecting morphism
`δ : L(Ext_φ) ⋙ D(Res_φ) ⟶ [1]` of `Mod.derivedExtendScalarsTriangleδ` is computed, on the image
of *any* complex `P` whose reduction sequence `0 ⟶ P --k--> P ⟶ S ⊗_R P ⟶ 0` is short exact (for
instance a complex of flat modules), by the connecting morphism of this short exact sequence
(`Mod.derivedExtendScalarsTriangleδ_app_Q_obj_of_shortExact`), and not only on the chosen
functorial K-flat resolution.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]
  (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)

/-- The connecting morphism of the reduction triangle on the image of a complex `P` whose
reduction sequence is short exact is the connecting morphism of this short exact sequence. -/
lemma derivedExtendScalarsTriangleδ_app_Q_obj_of_shortExact (P : CochainComplex (Mod C R) ℤ)
    (hS : (reductionShortComplex k w P).ShortExact) :
    (derivedExtendScalarsTriangleδ k w hφ).app (DerivedCategory.Q.obj P) =
      derivedExtendComapComparison φ P ≫ DerivedCategory.triangleOfSESδ hS := by
  let π := (CochainComplex.flatResolutionπ (Mod C R)).app P
  have h₁ := DerivedCategory.triangleOfSESδ_naturality
    (shortExact_extendUnitComplexHom k w hφ _ (CochainComplex.flat_flatResolutionFunctor_obj_X P))
    hS (reductionShortComplexMap k w π)
  have h₂ := derivedExtendComapComparison_naturality φ π
  simp only [reductionShortComplexMap_τ₁, reductionShortComplexMap_τ₃] at h₁
  rw [derivedExtendScalarsTriangleδ_app_Q_obj, reductionδComplex, h₁, ← reassoc_of% h₂,
    ← Functor.map_comp_assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The connecting morphism of the reduction triangle on the image in the derived category of a
complex `P` (through the homotopy category) whose reduction sequence is short exact. -/
lemma derivedExtendScalarsTriangleδ_app_Qh_obj_of_shortExact (P : CochainComplex (Mod C R) ℤ)
    (hS : (reductionShortComplex k w P).ShortExact) :
    (derivedExtendScalarsTriangleδ k w hφ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) =
      derivedExtendComapComparisonh φ P ≫
        (DerivedCategory.quotientCompQhIso (Mod C R)).hom.app
          ((extendComapComplexFunctor φ).obj P) ≫
        DerivedCategory.triangleOfSESδ hS ≫
        ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P)⟦(1 : ℤ)⟧' := by
  have h := (derivedExtendScalarsTriangleδ k w hφ).naturality
    ((DerivedCategory.quotientCompQhIso (Mod C R)).hom.app P)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  rw [← cancel_mono (((DerivedCategory.quotientCompQhIso (Mod C R)).hom.app P)⟦(1 : ℤ)⟧'), ← h,
    derivedExtendScalarsTriangleδ_app_Q_obj_of_shortExact k w hφ P hS, derivedExtendComapComparison]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

end CategoryTheory.Mod
