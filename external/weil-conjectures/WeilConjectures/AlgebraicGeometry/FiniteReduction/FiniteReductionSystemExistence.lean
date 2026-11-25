/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionSystem
import WeilConjectures.AlgebraicGeometry.FiniteReduction.System.FiniteReductionSystemCoherence
import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionDerivedExtension
import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionFlatExtension
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

set_option linter.privateModule false

/-! Construction of normalized coherent finite reduction systems. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u vC vD vH vK wC wD wH wK uC uD uH uK
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.FiniteReduction

attribute [local irreducible] extend ordinaryComparison ordinaryAssociator

private def compositeCounit
    {C D H : Type*} [Category C] [Category D] [Category H]
    [Abelian C] [Abelian D] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    (F : C ⥤ D) (G : D ⥤ H) (FG : C ⥤ H)
    [F.Additive] [G.Additive] [FG.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory H)
    (εF : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (i : F ⋙ G ≅ FG) : DerivedCategory.Q ⋙ (LF ⋙ LG) ⟶
      FG.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight εF LG ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) εG ≫
    Functor.whiskerRight (Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom
      DerivedCategory.Q

private theorem reverse_normalization
    {C : Type*} [Category C] {X Y Z W : C}
    (i : X ≅ Y) (α : Y ⟶ Z) (β : X ⟶ W) (e : Z ≅ W)
    (h : i.hom ≫ α = β ≫ e.inv) : i.inv ≫ β = α ≫ e.hom := by
  apply (cancel_epi i.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp

private theorem quotient_surjective (l : ℕ) {r m : ℕ} (h : m ≤ r) :
    Function.Surjective (quotient.{u} l h) := by
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow l h) y.down.down
  exact ⟨⟨⟨x⟩⟩, congrArg (fun z ↦ (⟨⟨z⟩⟩ : Coeff.{u} l m)) hx⟩

end AlgebraicGeometry.FiniteReduction
