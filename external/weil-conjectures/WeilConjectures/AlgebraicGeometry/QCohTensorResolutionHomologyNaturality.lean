/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparison
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinear

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact-functor homology comparison transports a commuting chain square. -/
theorem tensorResolution_homology_square
    {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι)
    {A B : HomologicalComplex C c} {A' B' : HomologicalComplex D c}
    (a : A ⟶ B) (b : A' ⟶ B')
    (s : (F.mapHomologicalComplex c).obj A ⟶ A')
    (t : (F.mapHomologicalComplex c).obj B ⟶ B')
    (h : (F.mapHomologicalComplex c).map a ≫ t = s ≫ b) :
    F.map (HomologicalComplex.homologyMap a i) ≫
        ((B.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap t i =
      ((A.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap s i ≫
        HomologicalComplex.homologyMap b i := by
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor C c i).map a) F
  change F.map (HomologicalComplex.homologyMap a i) ≫
      ((B.sc i).mapHomologyIso F).inv =
    ((A.sc i).mapHomologyIso F).inv ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map a) i at hn
  rw [reassoc_of% hn, ← HomologicalComplex.homologyMap_comp, h,
    HomologicalComplex.homologyMap_comp]

end AlgebraicGeometry
