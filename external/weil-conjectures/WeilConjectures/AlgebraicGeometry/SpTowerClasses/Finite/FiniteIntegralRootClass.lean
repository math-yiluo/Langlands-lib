/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses

/-! # Exact comparison of an integral root class

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-integral-root-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local instance 100001] finiteIntegralTowerDerived finiteIntegralTowerExt
  finiteIntegralAbDerived finiteIntegralAbExt finiteIntegralEtaleDerived finiteIntegralEtaleExt

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- The comparison image of an arbitrary degree-two etale root class, with the
canonical integral source and roots endpoints. Source: Stacks 03PL and exact site
comparison (blueprint: def-sfb-finite-integral-root-class). -/
def finiteIntegralRootClass (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ)
    (x : Sheaf.H (T.rootsOfUnitySheaf (l ^ (n + 1))) 2) :
    FiniteIntegralBoundaryArrow l T n :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv ≫
    mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ) x.hom ≫
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (cartierRootsComparison T (l ^ (n + 1))))⟦(2 : ℤ)⟧'

/-- The cached root class uses the actual integer and roots comparisons.
Source: the definition of finiteIntegralRootClass
(blueprint: def-sfb-finite-integral-root-class). -/
theorem finiteIntegralRootClass_eq (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ)
    (x : Sheaf.H (T.rootsOfUnitySheaf (l ^ (n + 1))) 2) :
    finiteIntegralRootClass l T n x =
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv ≫
        mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ) x.hom ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierRootsComparison T (l ^ (n + 1))))⟦(2 : ℤ)⟧' := by rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
