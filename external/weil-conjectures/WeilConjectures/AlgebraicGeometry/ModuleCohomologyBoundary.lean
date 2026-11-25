/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! # The canonical boundary in module cohomology

Source: Stacks Project, Cohomology, Tags 01DZ and 0B8S
(blueprint: def-sc-module-cohomology-boundary).
-/

@[expose] public section

universe uB wCB wDB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.RingedSpace

/-- The connecting map is the homology boundary of the image under derived global sections
of the canonical triangle of a short exact sequence. It is transported to the established
right-derived cohomology functors by the canonical single-complex comparison isomorphisms.
The triangle is `CategoryTheory.ShortComplex.ShortExact.singleTrianglePlus`; the displayed
expression is the right-hand side of the second conjunct of
`CategoryTheory.rightDerived_triangle_connecting` for `v = Γ(X, -)`.
Source: Stacks Project, Cohomology, Tags 01DZ and 0B8S
(blueprint: def-sc-module-cohomology-boundary). -/
noncomputable def moduleCohomologyBoundary (X : RingedSpace.{uB})
    [HasDerivedCategory.{wCB} (SheafOfModules.{uB} (moduleRings X))]
    [HasDerivedCategory.{wDB} (ModuleCat.{uB} ((moduleRings X).obj.obj (Opposite.op ⊤)))]
    (S : ShortComplex (SheafOfModules.{uB} (moduleRings X))) (hS : S.ShortExact)
    (q : ℕ) : (moduleCohomology X q).obj S.X₃ ⟶
      (moduleCohomology X (q + 1)).obj S.X₁ :=
  letI : EnoughInjectives (SheafOfModules.{uB} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  ((globalSectionsFunctor X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).inv.app S.X₃ ≫
    DerivedCategory.HomologySequence.δ
      (((globalSectionsFunctor X).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι).mapTriangle.obj hS.singleTrianglePlus)
      q (q + 1) (Nat.cast_add_one q).symm ≫
    ((globalSectionsFunctor X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      (q + 1)).hom.app S.X₁

end AlgebraicGeometry.RingedSpace
