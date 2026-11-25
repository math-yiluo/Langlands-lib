/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartModel
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionAugmentationComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinearTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionChartComponents_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionChartComponents_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionChartComponents_localInst3 (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionChartComponents_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The chart augmentation has the supplied degree-zero augmentation. -/
theorem tensorResolutionChartAugmentation_f_zero {Y : Scheme.{u}}
    (M : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1)) (P : ProjectiveResolution MA) :
    (tensorResolutionChartAugmentation M U MA sM P).f 0 ≫
        (Scheme.Modules.restrictFunctor U.2.fromSpec).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom =
      tilde.map ((P.complex.extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := 0) rfl).hom ≫ P.π.f 0) ≫
        (tensorResolutionChartModel M U MA sM).hom := by
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let e := tensorResolutionChartModel M U MA sM
  let S := CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0
  have hs : (S.map e.hom).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tilde MA)).hom ≫ e.hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (R.obj M)).inv :=
    HomologicalComplex.single_map_f_self (.up ℤ) 0 e.hom
  have ht : ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app M).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (R.obj M)).hom ≫
        R.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self R (.up ℤ) 0 M
  change ((tensorResolutionTildeAugmentation _ MA P).f 0 ≫ (S.map e.hom).f 0 ≫
    ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app M).inv.f 0) ≫
      R.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = _
  rw [hs, ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]
  rw [reassoc_of% tensorResolutionTildeAugmentation_f_zero]
  erw [Category.comp_id]

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The sheafified extension agrees with the original semilinear map in its degrees. -/
theorem tensorResolutionSemilinearComplexMap_extend_f
    {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex c).obj F)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (Scheme.Modules.restrictFunctor (Spec.map φ)).map (tilde.map (E.extendXIso e h).hom) ≫
        tensorResolutionSemilinearMap φ (a.f i) =
      (tensorResolutionSemilinearComplexMap φ c' (E.extend e) (F.extend e)
        (tensorResolutionExtendSemilinear φ.hom e E F a)).f i' ≫
          tilde.map (F.extendXIso e h).hom := by
  change _ = tensorResolutionSemilinearMap φ
    ((tensorResolutionExtendSemilinear φ.hom e E F a).f i') ≫ _
  rw [tensorResolutionSemilinearMap_precomp,
    tensorResolutionSemilinearMap_postcomp,
    tensorResolutionExtendSemilinear_f φ.hom e E F a h]
  congr 1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- A map out of an affine associated module is detected by its prescribed sections. -/
theorem tensorResolutionChartModel_naturality_from {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsQuasicoherent] (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sB : MB ≃ₗ[Γ(Y, V.1)] M.val.obj (op V.1))
    (E : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (f : E ⟶ MA)
    (g : E ⟶ (ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).obj MB)
    (hg : ∀ x, sB (g x) = M.val.map (homOfLE h).op (sA (f x))) :
    (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
        (tilde.map f ≫ (tensorResolutionChartModel M U MA sA).hom) ≫
        (tensorResolutionChartRestrictionIso Y V U h).hom.app M =
      tensorResolutionSemilinearMap (Y.presheaf.map (homOfLE h).op) g ≫
        (tensorResolutionChartModel M V MB sB).hom := by
  let φ := Y.presheaf.map (homOfLE h).op
  let eA := tensorResolutionChartModel M U MA sA
  let eB := tensorResolutionChartModel M V MB sB
  let t := tilde.map f ≫ eA.hom
  apply ((tensorResolutionSemilinearAdjunction φ).homEquiv E
    (M.restrict V.2.fromSpec)).injective
  apply ModuleCat.hom_ext
  ext m
  change ((tensorResolutionChartRestrictionIso Y V U h).hom.app M).app ⊤
      (((Scheme.Modules.restrictFunctor (Spec.map φ)).map t).app ⊤
        (((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app (tilde E)).app ⊤
          (tilde.toOpen E ⊤ m))) =
    eB.hom.app ⊤ ((tensorResolutionSemilinearMap φ g).app ⊤
      (((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app (tilde E)).app ⊤
        (tilde.toOpen E ⊤ m)))
  have hu := congrArg (fun a ↦ a.app ⊤ (tilde.toOpen E ⊤ m))
    ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.naturality t)
  change ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app
      (M.restrict U.2.fromSpec)).app ⊤ (t.app ⊤ (tilde.toOpen E ⊤ m)) =
    (((Scheme.Modules.restrictFunctor (Spec.map φ)).map t).app ⊤
      (((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app (tilde E)).app ⊤
        (tilde.toOpen E ⊤ m))) at hu
  rw [← hu, tensorResolutionSemilinearMap_unit]
  apply (Scheme.Modules.sectionsRestrictFromSpecLinearEquiv M V.2).injective
  rw [tensorResolutionChartRestriction_sections]
  dsimp only [t, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hf := congr($(tilde.toOpen_map_app f ⊤) m)
  change (tilde.map f).app ⊤ (tilde.toOpen E ⊤ m) = tilde.toOpen MA ⊤ (f m) at hf
  dsimp only [eA, eB]
  simp only [ConcreteCategory.comp_apply]
  rw [hf, tensorResolutionChartModel_toOpen, tensorResolutionChartModel_toOpen,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact (hg m).symm

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Inverse-degree normalization for the sheafified semilinear extension. -/
theorem tensorResolutionSemilinearComplexMap_extend_inv_f
    {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex c).obj F)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (Scheme.Modules.restrictFunctor (Spec.map φ)).map (tilde.map (E.extendXIso e h).inv) ≫
        (tensorResolutionSemilinearComplexMap φ c' (E.extend e) (F.extend e)
          (tensorResolutionExtendSemilinear φ.hom e E F a)).f i' =
      tensorResolutionSemilinearMap φ (a.f i) ≫ tilde.map (F.extendXIso e h).inv := by
  change _ ≫ tensorResolutionSemilinearMap φ
    ((tensorResolutionExtendSemilinear φ.hom e E F a).f i') = _
  rw [tensorResolutionSemilinearMap_precomp,
    tensorResolutionSemilinearMap_postcomp,
    tensorResolutionExtendSemilinear_f φ.hom e E F a h]
  congr 1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The chart coefficient comparison is natural in its literal single complex. -/
theorem tensorResolutionChartCoefficient_naturality {Y : Scheme.{u}} (N : Y.Modules)
    [N.IsQuasicoherent] (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (b : NA ⟶ (ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).obj NB)
    (hb : ∀ x, sB (b x) = N.val.map (homOfLE h).op (sA x)) :
    (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
        ((tensorResolutionChartModel N U NA sA).hom ≫
          (Scheme.Modules.restrictFunctor U.2.fromSpec).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv) ≫
        (tensorResolutionChartRestrictionIso Y V U h).hom.app
          (((CochainComplex.singleFunctor Y.Modules 0).obj N).X 0) =
      tensorResolutionSemilinearMap (Y.presheaf.map (homOfLE h).op) b ≫
        (tensorResolutionChartModel N V NB sB).hom ≫
          (Scheme.Modules.restrictFunctor V.2.fromSpec).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv := by
  have hn := (tensorResolutionChartRestrictionIso Y V U h).hom.naturality
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
  change (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
      ((Scheme.Modules.restrictFunctor U.2.fromSpec).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv) ≫
      (tensorResolutionChartRestrictionIso Y V U h).hom.app _ =
    (tensorResolutionChartRestrictionIso Y V U h).hom.app N ≫
      (Scheme.Modules.restrictFunctor V.2.fromSpec).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv at hn
  rw [Functor.map_comp, Category.assoc]
  erw [hn]
  rw [← Category.assoc, tensorResolutionChartModel_naturality N V U h NA NB sA sB b hb]
  rfl

end AlgebraicGeometry
