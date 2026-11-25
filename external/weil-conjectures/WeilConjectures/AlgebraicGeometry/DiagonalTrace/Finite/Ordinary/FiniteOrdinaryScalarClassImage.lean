/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryScalarClass
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Exact image of the realized ordinary scalar class

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-ordinary-scalar-class-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ t₁ t₂ t₃
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses SpTowerClasses.FiniteExactArrow

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors

/-- Any exact functor sends the realized ordinary scalar class to the image
of the integral generator followed by its twice-transported ordinary arrow.
Source: ordinaryFiniteClass_hom and naturality of the exact single comparison
(blueprint: lem-sfb-finite-ordinary-scalar-class-image).

Proof: substitute the realized scalar-class formula, then use exact single-arrow
naturality for precomposition by the integral generator. The target category,
exact functor and coefficient ring are arbitrary. -/
theorem ordinaryFiniteClass_exact_image (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{t₂} D]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : Etale.ordinaryFiniteUnit A T ⟶
      ((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧) :
    mapSingleArrow F (2 : ℤ) (Etale.ordinaryFiniteClass A T M 2 a).hom =
      (DerivedCategory.singleFunctor D 0).map
          (F.map (Etale.ordinaryFiniteIntegralGenerator A T)) ≫
        mapSingleArrow F (2 : ℤ)
          (mapSingleArrow (Etale.moduleAbelianForget A T) (2 : ℤ) a) := by
  rw [ordinaryFiniteClass_hom, mapSingleArrow_precomp]

/-- The exact scalar-class formula remains valid after arbitrary derived
source and target normalizations. Source: the preceding exact image formula
and associativity (blueprint: lem-sfb-finite-ordinary-scalar-class-image).

Proof: substitute ordinaryFiniteClass_exact_image on the right and associate
both composites. All normalization arrows are arbitrary. -/
theorem ordinaryFiniteClass_exact_image_prepost (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{t₂} D]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : Etale.ordinaryFiniteUnit A T ⟶
      ((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧)
    {X Y : DerivedCategory D}
    (i : X ⟶ (DerivedCategory.singleFunctor D 0).obj
      (F.obj ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
    (r : ((DerivedCategory.singleFunctor D 0).obj
      (F.obj ((Etale.moduleAbelianForget A T).obj M)))⟦(2 : ℤ)⟧ ⟶ Y) :
    i ≫ (DerivedCategory.singleFunctor D 0).map
          (F.map (Etale.ordinaryFiniteIntegralGenerator A T)) ≫
        mapSingleArrow F (2 : ℤ)
          (mapSingleArrow (Etale.moduleAbelianForget A T) (2 : ℤ) a) ≫ r =
      i ≫ mapSingleArrow F (2 : ℤ) (Etale.ordinaryFiniteClass A T M 2 a).hom ≫ r := by
  rw [ordinaryFiniteClass_exact_image]
  simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.DiagonalTrace
