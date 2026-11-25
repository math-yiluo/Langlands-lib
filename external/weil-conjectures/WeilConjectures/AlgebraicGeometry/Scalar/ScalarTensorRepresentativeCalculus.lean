/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Upper.UpperStarSingleTensorRepresentative

/-!
# Scalar tensor representatives with their specified derived endpoints

## References

* Stacks Project, Tags 06YY, 07A4 and 0FPH
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar

private theorem tensor_representative_isIso
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (M : C) (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (tensorSingleRepresentative M P) := by
  have h : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M))) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) := by
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (HomotopyCategory.quotient _ (.up ℤ)) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M))) ≫ _)
    infer_instance
  dsimp only [tensorSingleRepresentative]
  infer_instance

private theorem comp_complex_id
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (P : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P =
      𝟙 _ := by
  ext i
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom,
    NatTrans.id_app, HomologicalComplex.id_f]
  rfl

private theorem map_comp_complex_id
    {C D E K : Type*} [Category C] [Category D] [Category E] [Category K]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (H : CochainComplex E ℤ ⥤ K) (P : CochainComplex C ℤ) :
    H.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P) =
      𝟙 _ := by
  rw [comp_complex_id]
  exact H.map_id _

private theorem normalized_tensor_representative
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
    [Abelian.HasFunctorialFlatResolution C]
    (V : C ⥤ D) (U : D ⥤ C) [V.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (E : DerivedCategory C ⥤ DerivedCategory D) (S : C)
    (τ : tensorRight S ⟶ V ⋙ U)
    (e : E ⋙ U.mapDerivedCategory ≅ scalarTensorModelFunctor S)
    (r : ∀ P : CochainComplex C ℤ, E.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P))
    (hn : scalarTensorModelNormalization S τ e (fun P ↦
      U.mapDerivedCategory.map (r P) ≫
        U.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (V ⋙ U)) (.up ℤ)).hom.app P)))
    (P : CochainComplex C ℤ) :
    e.hom.app (DerivedCategory.Q.obj P) ≫ tensorSingleRepresentative S P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) =
      U.mapDerivedCategory.map (r P) ≫
        U.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := hn P
  dsimp only at h
  rw [map_comp_complex_id] at h
  erw [Category.comp_id] at h
  simpa only [tensorSingleRepresentative, Category.assoc] using h

/-- The localization tensor representative with the scalar tensor functor's endpoint. -/
def scalarTensorRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (scalarCoefficient φ T)).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((tensorRight (scalarCoefficientSheaf φ T)).mapHomologicalComplex (.up ℤ)).obj P) :=
  (eqToIso (scalarTensorFunctor_eq φ T)).hom.app (DerivedCategory.Q.obj P) ≫
    tensorSingleRepresentative (scalarCoefficientSheaf φ T) P

/-- The scalar/tensor normalization with the functor transport kept explicit. -/
theorem scalarTensorIso_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarTensorIso φ T).hom.app (DerivedCategory.Q.obj P) ≫
        scalarTensorRepresentative φ T P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (scalarSheafTensorTransformation φ T)
            (.up ℤ)).app P) =
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
          (scalarExtensionRepresentative φ T P) ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.hom.app
          (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := normalized_tensor_representative
    (ProEtale.etaleSheafExtendScalars φ T) (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (scalarExtension φ T) (scalarCoefficientSheaf φ T) (scalarSheafTensorTransformation φ T)
    ((scalarTensorIso φ T) ≪≫ eqToIso (scalarTensorFunctor_eq φ T))
    (scalarExtensionRepresentative φ T) (scalarTensorIso_existsUnique φ T).choose_spec.1 P
  simpa only [scalarTensorRepresentative, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc] using h

/-- The scalar tensor representative is invertible on a K-flat first factor. -/
theorem scalarTensorRepresentative_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (scalarTensorRepresentative φ T P) := by
  have := tensor_representative_isIso (scalarCoefficientSheaf φ T) P hP
  dsimp only [scalarTensorRepresentative]
  infer_instance

end AlgebraicGeometry.Etale
