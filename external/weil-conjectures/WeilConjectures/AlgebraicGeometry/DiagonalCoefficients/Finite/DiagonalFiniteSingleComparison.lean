/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology

/-! # Exact single comparison with the cached ordinary embedding -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
section
attribute [local instance 100000] CategoryTheory.sheafIsAbelian
attribute [local instance 100000] AlgebraicGeometry.Etale.ordinaryFiniteDerivedCategoryInstance
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The exact comparison with the existing cached etale single embedding.
Source: diagonal coefficient changes (1), the finite constant unit comparison.
(blueprint: def-diagonal-finite-single-comparison).

This is the canonical exact-derived single comparison. Its functor interface uses
`ordinaryFiniteSingleFunctor`, so its component objects retain the existing
`ordinaryFiniteDegreeZero` presentation before the comparison functor is applied. -/
def finiteSingleComparison (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Etale.ordinaryFiniteSingleFunctor A X ⋙ geoP1Comparison A X ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0 :=
  Functor.isoWhiskerRight (eqToIso (Etale.ordinaryFiniteSingleFunctor_eq A X)) _ ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0

private theorem whisker_eqToIso_trans_heq {C D E : Type*}
    [Category C] [Category D] [Category E] {S T : C ⥤ D}
    {F : D ⥤ E} {G : C ⥤ E} (h : S = T) (e : T ⋙ F ≅ G) :
    HEq (Functor.isoWhiskerRight (eqToIso h) F ≪≫ e) e := by
  subst T
  simp

/-- The cached comparison is the canonical exact-derived comparison after identifying
its source single functor. Source: the exact-derived comparison in coefficient changes (1).
(blueprint: def-diagonal-finite-single-comparison).
Proof: transport along the cached-functor equality and eliminate that equality. -/
theorem finiteSingleComparison_heq (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HEq (finiteSingleComparison A X)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0) := by
  exact whisker_eqToIso_trans_heq (Etale.ordinaryFiniteSingleFunctor_eq A X) _

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
end
