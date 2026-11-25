/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Scalar compatibility of exact derived factorization

Source: Stacks Project, Derived Categories, Tag 015F.
(blueprint: lem-weil-pbc-scalar-localization-unit-factors)
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' w w' r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A normalized termwise unit intertwines target scalars under derived factorization.
Source: Stacks Project, Derived Categories, Tag 015F.
(blueprint: lem-weil-pbc-scalar-localization-unit-factors).
Proof: commute the scalar through the extension factorization isomorphism by
bilinearity; then use naturality of the restriction factorization and the unit
normalization. No linearity of restriction over the target ring is required. -/
theorem scalarLocalization_unit_factors
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {B' : Type u'} [Category.{v'} B'] [Abelian B'] [HasDerivedCategory.{w'} B']
    (S : Type r) [CommRing S] [Linear S B']
    (E : B ⥤ B') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : B' ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E.mapDerivedCategory ⊣ U.mapDerivedCategory)
    (K : CochainComplex B ℤ)
    (η : K ⟶ (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hη : adj.unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) = DerivedCategory.Q.map η)
    (s : S) :
    DerivedCategory.Q.map (η ≫ (U.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (s • 𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) =
      adj.unit.app (DerivedCategory.Q.obj K) ≫
        U.mapDerivedCategory.map (s • 𝟙 (E.mapDerivedCategory.obj (DerivedCategory.Q.obj K))) ≫
        U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
        U.mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let vK := s • 𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have hscalar : (s • 𝟙 (E.mapDerivedCategory.obj (DerivedCategory.Q.obj K))) ≫
      E.mapDerivedCategoryFactors.hom.app K = E.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map vK := by
    simp [vK, Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
  rw [Functor.map_comp, ← hη]
  change (adj.unit.app (DerivedCategory.Q.obj K) ≫
    U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
    U.mapDerivedCategoryFactors.hom.app _) ≫
    DerivedCategory.Q.map ((U.mapHomologicalComplex (ComplexShape.up ℤ)).map vK) = _
  rw [Category.assoc, Category.assoc,
    ← U.mapDerivedCategoryFactors_hom_naturality vK]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [hscalar]

end CategoryTheory
