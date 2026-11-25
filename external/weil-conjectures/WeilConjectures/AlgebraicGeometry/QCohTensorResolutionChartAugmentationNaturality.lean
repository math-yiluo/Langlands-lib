/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The supplied degree-zero augmentation equation gives the affine augmentation square. -/
theorem tensorResolutionChartAugmentation_naturality {Y : Scheme.{u}}
    (M : Y.Modules) [M.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sB : MB ≃ₗ[Γ(Y, V.1)] M.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB)
    (a : PA.complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj PB.complex)
    (ha : ∀ x : PA.complex.X 0,
      sB (PB.π.f 0 (a.f 0 x)) = M.val.map (homOfLE h).op (sA (PA.π.f 0 x))) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let RC := R.mapHomologicalComplex (.up ℤ)
    RC.map (tensorResolutionChartAugmentation M U MA sA PA) ≫
        (tensorResolutionChartRestrictionComplexIso Y V U h
          ((CochainComplex.singleFunctor Y.Modules 0).obj M)).hom =
      tensorResolutionSemilinearComplexMap φ (.up ℤ)
        (PA.complex.extend ComplexShape.embeddingDownNat)
        (PB.complex.extend ComplexShape.embeddingDownNat)
        (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex
          PB.complex a) ≫
          tensorResolutionChartAugmentation M V MB sB PB := by
  dsimp only
  let φ := Y.presheaf.map (homOfLE h).op
  let R := Scheme.Modules.restrictFunctor (Spec.map φ)
  let RU := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RV := Scheme.Modules.restrictFunctor V.2.fromSpec
  let rA := tensorResolutionChartAugmentation M U MA sA PA
  let rB := tensorResolutionChartAugmentation M V MB sB PB
  let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
    (PA.complex.extend ComplexShape.embeddingDownNat)
    (PB.complex.extend ComplexShape.embeddingDownNat)
    (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex PB.complex a)
  let S := CochainComplex.singleFunctor Y.Modules 0
  let χ := tensorResolutionChartRestrictionIso Y V U h
  have hn := χ.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom
  change R.map (RU.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom) ≫
      χ.hom.app M = χ.hom.app ((S.obj M).X 0) ≫
        RV.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom at hn
  have hc0 : R.map (rA.f 0) ≫ χ.hom.app ((S.obj M).X 0) ≫
      RV.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom =
    a'.f 0 ≫ rB.f 0 ≫ RV.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom := by
    rw [← hn, ← Functor.map_comp_assoc]
    rw [tensorResolutionChartAugmentation_f_zero M U MA sA PA,
      tensorResolutionChartAugmentation_f_zero M V MB sB PB]
    simp only [tilde.map_comp, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% tensorResolutionSemilinearComplexMap_extend_f φ
      ComplexShape.embeddingDownNat PA.complex PB.complex a (i := 0) (i' := 0) rfl]
    have : IsIso (R.map (tilde.map (PA.complex.extendXIso
        ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).hom)) := by
      change IsIso (R.map ((tilde.functor Γ(Y, U.1)).map
        (PA.complex.extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := 0) rfl).hom))
      infer_instance
    apply (cancel_epi (R.map (tilde.map (PA.complex.extendXIso
      ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).hom))).2
    have hg := tensorResolutionChartModel_naturality_from M V U h MA MB sA sB
      (PA.complex.X 0) (PA.π.f 0)
      (a.f 0 ≫ (ModuleCat.restrictScalars φ.hom).map (PB.π.f 0)) ha
    rw [← tensorResolutionSemilinearMap_postcomp] at hg
    simpa only [Functor.map_comp, Category.assoc] using hg
  apply (cancel_mono
    ((HomologicalComplex.singleMapHomologicalComplex RV (.up ℤ) 0).app M).hom).1
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RV.obj M)).hom).1
  simp only [HomologicalComplex.comp_f, Iso.app_hom, Functor.mapHomologicalComplex_map_f,
    tensorResolutionChartRestrictionComplexIso,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc, Iso.inv_hom_id]
  exact hc0

end AlgebraicGeometry
