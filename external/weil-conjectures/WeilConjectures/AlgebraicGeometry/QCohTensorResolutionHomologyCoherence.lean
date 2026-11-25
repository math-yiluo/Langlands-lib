/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionHomologyCoherence_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionHomologyCoherence_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionHomologyCoherence_localInst3 (X : Scheme.{u}) :
  (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionHomologyCoherence_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Normalized restriction of ordinary total tensor homology. -/
noncomputable def tensorResolutionNormalizedRestrictHomologyIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (E F : CochainComplex Y.Modules ℤ) (i : ℤ) :
    (Scheme.Modules.restrictFunctor j).obj
        ((CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)).homology i) ≅
      (CochainComplex.mapBifunctor
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E)
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F)
        (curriedTensor X.Modules)).homology i :=
  (((CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)).sc i).mapHomologyIso
    (Scheme.Modules.restrictFunctor j)).symm ≪≫
  (HomologicalComplex.homologyFunctor X.Modules (.up ℤ) i).mapIso
    (tensorResolutionRestrictionTotalIso j E F)

/-- Compose a homology comparison square with the comparison for two exact functors. -/
private theorem tensorResolution_normalized_homology_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]
    (e : F ⋙ G ≅ H) {ι : Type*} (c : ComplexShape ι) (i : ι)
    (A : HomologicalComplex C c) (B : HomologicalComplex D c)
    (B' : HomologicalComplex E c)
    (a : (F.mapHomologicalComplex c).obj A ≅ B)
    (b : (H.mapHomologicalComplex c).obj A ≅ B')
    (t : (G.mapHomologicalComplex c).obj B ⟶ B')
    (hc : (G.mapHomologicalComplex c).map a.hom ≫ t =
      ((Functor.mapHomologicalComplexCompIso e c).app A).hom ≫ b.hom) :
    G.map (((A.sc i).mapHomologyIso F).symm ≪≫
      (HomologicalComplex.homologyFunctor D c i).mapIso a).hom ≫
        ((B.sc i).mapHomologyIso G).inv ≫ HomologicalComplex.homologyMap t i =
      e.hom.app (A.homology i) ≫ (((A.sc i).mapHomologyIso H).symm ≪≫
        (HomologicalComplex.homologyFunctor E c i).mapIso b).hom := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor]
  rw [Functor.map_comp, Category.assoc]
  have h₁ := tensorResolution_homology_square G c i a.hom b.hom
    ((Functor.mapHomologicalComplexCompIso e c).app A).hom t hc
  have h₂ := tensorResolution_homology_composition F G H e.hom (A.sc i)
  rw [h₁]
  change G.map ((A.sc i).mapHomologyIso F).inv ≫
    (((A.sc i).map F).mapHomologyIso G).inv ≫
      ShortComplex.homologyMap ((A.sc i).mapNatTrans e.hom) ≫ _ = _
  rw [reassoc_of% h₂]
  rfl

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Nested chart restriction is compatible with normalized tensor homology. -/
theorem tensorResolutionNormalizedRestrictHomologyIso_naturality
    (Y : Scheme.{u}) (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (E F : CochainComplex Y.Modules ℤ) (i : ℤ)
    (hc :
      ((Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE
        h).op))).mapHomologicalComplex
        (.up ℤ)).map (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).hom ≫
        tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
          (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj F)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj F)
          (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
          (tensorResolutionChartRestrictionComplexIso Y V U h F).hom =
      (tensorResolutionChartRestrictionComplexIso Y V U h
        (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules))).hom ≫
          (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).hom) :
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let R := Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))
    R.map (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec E F i).hom ≫
      (((CochainComplex.mapBifunctor (RU.obj E) (RU.obj F)
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc i).mapHomologyIso R).inv ≫
      HomologicalComplex.homologyMap
        (tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
          (RU.obj E) (RU.obj F)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj F)
          (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
          (tensorResolutionChartRestrictionComplexIso Y V U h F).hom) i =
      (tensorResolutionChartRestrictionIso Y V U h).hom.app
        ((CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)).homology i) ≫
          (tensorResolutionNormalizedRestrictHomologyIso V.2.fromSpec E F i).hom := by
  have hn := tensorResolution_normalized_homology_naturality
    (Scheme.Modules.restrictFunctor U.2.fromSpec)
    (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op)))
    (Scheme.Modules.restrictFunctor V.2.fromSpec)
    (tensorResolutionChartRestrictionIso Y V U h) (.up ℤ) i
    (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)) _ _
    (tensorResolutionRestrictionTotalIso U.2.fromSpec E F)
    (tensorResolutionRestrictionTotalIso V.2.fromSpec E F) _ hc
  exact hn

end AlgebraicGeometry
