/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Upper.UpperStarSingleTensorDefinitions
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData

/-!
# The exact single-coefficient geometric representative

Source: Stacks Project, Tags 07A4 and 0FPH
(blueprint: lem-pur-upper-star-single-coefficient-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar
  Functor.leftDerivedFunctorCounit Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh

private theorem geometric_single_core
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D) (e : L ≅ F.mapDerivedCategory)
    {M : C} {N : D} (k : F.obj M ≅ N) :
    (e.app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
        (F.mapDerivedCategorySingleFunctor 0).app M ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso k).hom =
      Functor.exactDerivedRepresentative F L e
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map k.hom) := by
  simp only [Functor.exactDerivedRepresentative, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.mapDerivedCategorySingleFunctor_hom_app_eq, Category.assoc]
  have hs : (DerivedCategory.singleFunctor _ 0).map k.hom =
      DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map k.hom) := rfl
  rw [hs, CategoryTheory.Functor.map_comp]
  rfl

/-- The exact single-coefficient comparison is the geometric representative
followed by localization of the ordinary single-complex comparison and coefficient iso.
Source: Stacks Project, Tag 07A4
(blueprint: lem-pur-upper-star-single-coefficient-representative).
Proof: factor the geometric representative through the exact-derived comparison.
Use mapDerivedCategorySingleFunctor_hom_app_eq and functoriality of Q on the
single-complex comparison followed by k. The singleFunctor is single followed by Q. -/
theorem upperStar_single_coefficient_representative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    {M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N) :
    (upperStarSingleCoefficientIso A f k).hom =
    scalarGeometricRepresentative A f ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (upperStar (ModuleCat.{u + 1} A) f) (.up ℤ) 0).hom.app M ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map k.hom) := by
  rw [scalarGeometricRepresentative_exact]
  exact geometric_single_core (upperStar (ModuleCat.{u + 1} A) f)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) k

end AlgebraicGeometry.Etale
