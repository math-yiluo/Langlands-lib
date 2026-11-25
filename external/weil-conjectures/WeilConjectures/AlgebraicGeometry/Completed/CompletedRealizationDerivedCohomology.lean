/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Normalized completed realization on unbounded derived categories

Source: Stacks Project, Modules on Sites, Tags 093J and 093M; Derived Categories,
Tag 015F; Bhatt--Scholze, Propositions 6.6.11 and 6.8.11(3)
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).

The realization is the existing `integralConstantModule`, including restriction along
`(pbcCompletedComparison T d).inv`. The comparisons below are actual constructions from
termwise localization and the kernel/image/cokernel comparison, without chosen witnesses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

/-- Localization factorization of the termwise completed realization, with its canonical
normalization. Source: Stacks Tag 015F, parts (3)--(4)
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).
This is `mapDerivedCategoryFactors`, so its shift structure is the one descended from
identity maps on the terms of shifted complexes. -/
def integralRealizationFactors (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    completedConstantQ (ModuleCat.{u + 1} A) ⋙ integralConstantDerived T d ≅
      (integralConstantModule T d).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategoryFactors

end AlgebraicGeometry.Scheme
