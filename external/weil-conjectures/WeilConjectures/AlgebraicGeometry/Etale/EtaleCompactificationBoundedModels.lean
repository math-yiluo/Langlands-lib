/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.CategoryTheory.Right.RightDerivedSingleH0
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

set_option linter.privateModule false

/-! # Bounded models for an etale compactification

Source: Stacks Project, Tag 0GL6, bounded-model preparation using the prescribed
etale compact-support normalization (blueprint: lem-sp-etale-compactification-bounded-models).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Sheaf.instHasColimitsOfShape
  Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] lowerStar upperStar Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorUnitQ

private theorem comparison_cancel
    {C : Type*} [Category C] {X Y Z W : C}
    (s : X ≅ Y) (a : Y ≅ Z) (t : W ≅ X) (f : Z ⟶ W)
    (h : s.hom ≫ a.hom ≫ f = t.inv) : f ≫ t.hom ≫ s.hom = a.inv := by
  apply (cancel_epi (s.hom ≫ a.hom)).1
  calc
    _ = (s.hom ≫ a.hom ≫ f) ≫ t.hom ≫ s.hom := by simp only [Category.assoc]
    _ = s.hom := by rw [h]; simp only [Iso.inv_hom_id_assoc]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem acyclicComparison_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (O : C ⥤ D) (F : D ⥤ E) [O.Additive] [F.Additive]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    {K L : CochainComplex C ℤ} (phi : K ⟶ L) :
    DerivedCategory.Q.map (((O ⋙ F).mapHomologicalComplex (.up ℤ)).map phi) ≫
        (F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L) ≫
          F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app L)) =
      (F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app K)) ≫
        F.rightDerivedFunctor.map (O.mapDerivedCategory.map (DerivedCategory.Q.map phi)) := by
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
    ((O.mapHomologicalComplex (.up ℤ)).map phi)) ≫ _ = _
  rw [Functor.rightDerivedFunctorUnitQ_naturality_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg F.rightDerivedFunctor.map
    (NatTrans.naturality O.mapDerivedCategoryFactors.inv phi)

private theorem normalization_complex
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (F : D ⥤ E)
    [S.Additive] [O.Additive] [F.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (a : S ⟶ O ⋙ F)
    (σ : S.mapDerivedCategory ⟶ O.mapDerivedCategory ⋙ F.rightDerivedFunctor)
    (hσ : ∀ J : HomotopyCategory C (.up ℤ),
      σ.app (DerivedCategory.Qh.obj J) =
        S.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app J) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ F)) (.up ℤ)).inv.app J) ≫
        F.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj J) ≫
        F.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app J))
    (L : CochainComplex C ℤ) :
    S.mapDerivedCategoryFactors.hom.app L ≫
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app L) ≫
      F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L) ≫
      F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app L) =
      σ.app (DerivedCategory.Q.obj L) := by
  have h := comparison_complex_fac S O F a σ hσ L
  have hu : right_unit_Q F ((O.mapHomologicalComplex (.up ℤ)).obj L) =
      F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L) := by
    unfold right_unit_Q Functor.rightDerivedFunctorUnitQ
    rfl
  rw [hu] at h
  calc
    _ = (S.mapDerivedCategoryFactors.hom.app L ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app L) ≫
        F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app L) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [← h]
      simp only [Category.assoc, ← F.rightDerivedFunctor.map_comp, Iso.hom_inv_id_app]
      erw [F.rightDerivedFunctor.map_id, Category.comp_id]

end AlgebraicGeometry.Etale
