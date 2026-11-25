/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTensorNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionTotalComponents_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionTotalComponents_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionTotalComponents_localInst3 (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionTotalComponents_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Total tensor maps on their coproduct summands. -/
@[reassoc] theorem tensorResolution_ι_totalTensorMap {X : Scheme.{u}}
    {E E' F F' : CochainComplex X.Modules ℤ} (a : E ⟶ E') (b : F ⟶ F')
    (p q i : ℤ) (h : p + q = i) :
    HomologicalComplex.ιMapBifunctor E F (curriedTensor X.Modules) (.up ℤ) p q i h ≫
        (HomologicalComplex.mapBifunctorMap a b (curriedTensor X.Modules) (.up ℤ)).f i =
      (a.f p ⊗ₘ b.f q) ≫
        HomologicalComplex.ιMapBifunctor E' F' (curriedTensor X.Modules) (.up ℤ) p q i h := by
  rw [tensorHom_def]
  exact HomologicalComplex.ι_mapBifunctorMap a b (curriedTensor X.Modules) (.up ℤ) p q i h

/-- Forward restriction comparison on one total tensor summand. -/
@[reassoc] theorem tensorResolution_map_ι_restrictionTotal_hom {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (E F : CochainComplex Y.Modules ℤ)
    (p q i : ℤ) (h : p + q = i) :
    (Scheme.Modules.restrictFunctor j).map
        (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i h) ≫
        (tensorResolutionRestrictionTotalIso j E F).hom.f i =
      (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F)
          (curriedTensor X.Modules) (.up ℤ) p q i h := by
  dsimp only [tensorResolutionRestrictionTotalIso, asIso_hom,
    HomologicalComplex.mapBifunctorComparison_f]
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (tensorResolutionRestrictionTensorNatIso j).hom (.up ℤ) E F p q i h

/-- Inverse restriction comparison on one total tensor summand. -/
@[reassoc] theorem tensorResolution_ι_restrictionTotal_inv {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (E F : CochainComplex Y.Modules ℤ)
    (p q i : ℤ) (h : p + q = i) :
    HomologicalComplex.ιMapBifunctor
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E)
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F)
        (curriedTensor X.Modules) (.up ℤ) p q i h ≫
        (tensorResolutionRestrictionTotalIso j E F).inv.f i =
      (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).inv ≫
        (Scheme.Modules.restrictFunctor j).map
          (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i h) := by
  apply (cancel_mono ((tensorResolutionRestrictionTotalIso j E F).hom.f i)).1
  have hi : (tensorResolutionRestrictionTotalIso j E F).inv.f i ≫
      (tensorResolutionRestrictionTotalIso j E F).hom.f i = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f ↦ f.f i) (tensorResolutionRestrictionTotalIso j E F).inv_hom_id
  rw [Category.assoc, hi, Category.comp_id]
  dsimp only [tensorResolutionRestrictionTotalIso, asIso_hom,
    HomologicalComplex.mapBifunctorComparison_f]
  rw [Category.assoc, HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  change _ = (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).inv ≫
    (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).hom ≫ _
  simp

end AlgebraicGeometry
