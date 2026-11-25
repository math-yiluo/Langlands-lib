/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartModel
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTensorNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartTensorTailMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance trChartTensorTailPreadditive
    (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance trChartTensorTailZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartTensorTailObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The single-object and total-tensor factors of the chart tensor comparison. -/
theorem tensorResolutionChartTensor_tail {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ProjectiveResolution MA) (j : ℕ) :
    let i := -(j : ℤ)
    let E := tensorResolutionChartComplex U MA P
    let B := ((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor Y.Modules 0).obj N)
    let eN := (CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
      (tensorResolutionChartModel N U NA sN).hom ≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app N).inv
    tensorResolutionTildeTensorHom _ (P.complex.X j) NA ≫
      ((tensorRight (tilde NA)).map
        (tilde.map (P.complex.extendXIso ComplexShape.embeddingDownNat
          (i := j) (i' := i) rfl).inv)) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
          (tilde NA) E).inv.f i ≫
        (((curriedTensor _).map₂CochainComplex.obj E).map eN).f i =
      tensorResolutionTildeTensorHom _ (P.complex.X j) NA ≫
        (tilde.map (P.complex.extendXIso ComplexShape.embeddingDownNat
            (i := j) (i' := i) rfl).inv ⊗ₘ
          ((tensorResolutionChartModel N U NA sN).hom ≫
            (Scheme.Modules.restrictFunctor U.2.fromSpec).map
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)) ≫
        HomologicalComplex.ιMapBifunctor E B (curriedTensor _) (.up ℤ) i 0 i (by simp) := by
  dsimp only
  let E := tensorResolutionChartComplex U MA P
  let eN := (CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
    (tensorResolutionChartModel N U NA sN).hom ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app N).inv
  dsimp only [Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
  simp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_inv, Iso.symm_inv,
    HomologicalComplex.comp_f]
  have hflip := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
    (𝟙 E) eN (curriedTensor (Spec Γ(Y, U.1)).Modules) (.up ℤ)
  have hflipf := congrArg (fun h ↦ h.f (-(j : ℤ))) hflip
  have hflipf' := by simpa only [HomologicalComplex.comp_f] using hflipf
  dsimp [E] at hflipf'
  dsimp [tensorResolutionChartComplex]
  simp only [Category.assoc]
  erw [← hflipf']
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  simp only [Category.assoc]
  have hi := HomologicalComplex.ι_mapBifunctorMap eN (𝟙 E)
    (curriedTensor (Spec Γ(Y, U.1)).Modules).flip (.up ℤ) 0 (-(j : ℤ))
      (-(j : ℤ)) (by simp)
  dsimp [E] at hi
  congr 1
  unfold tensorResolutionChartComplex at hi
  unfold tensorResolutionChartComplex
  change
      ((HomologicalComplex.single (Spec Γ(Y, U.1)).Modules (.up ℤ) 0).obj
          (tilde NA)).ιMapBifunctor
          (((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
            (P.complex.extend ComplexShape.embeddingDownNat))
          (curriedTensor (Spec Γ(Y, U.1)).Modules).flip (.up ℤ) 0 (-(j : ℤ))
            (-(j : ℤ)) (by simp) ≫
        (HomologicalComplex.mapBifunctorMap eN
          (𝟙 (((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
            (P.complex.extend ComplexShape.embeddingDownNat)))
          (curriedTensor (Spec Γ(Y, U.1)).Modules).flip (.up ℤ)).f (-(j : ℤ)) = _ at hi
  rw [reassoc_of% hi]
  change ((curriedTensor (Spec Γ(Y, U.1)).Modules).map _).app _ ≫ _ = _
  simp only [curriedTensor_map_app, Functor.flip_map_app, curriedTensor_obj_map]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  have heN :
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tilde NA)).inv ≫ eN.f 0 =
        (tensorResolutionChartModel N U NA sN).hom ≫
          (Scheme.Modules.restrictFunctor U.2.fromSpec).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv := by
    dsimp [eN]
    simp [CochainComplex.singleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc]
  rw [tensorHom_def]
  simp only [← curriedTensor_map_app, ← curriedTensor_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.assoc]
  have hmap := ((curriedTensor (Spec Γ(Y, U.1)).Modules).obj
      ((((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
        (P.complex.extend ComplexShape.embeddingDownNat)).X (-(j : ℤ)))).map_comp
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tilde NA)).inv) (eN.f 0)
  erw [← reassoc_of% hmap, heN]
  have hs : (ComplexShape.up ℤ).σ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (-(j : ℤ)) 0 = 1 := by simp [ComplexShape.σ]
  rw [hs, one_smul]
  change _ ≫ _ ≫ (𝟙 _ ≫ _) = _
  rw [Category.id_comp]
  rfl

end AlgebraicGeometry
