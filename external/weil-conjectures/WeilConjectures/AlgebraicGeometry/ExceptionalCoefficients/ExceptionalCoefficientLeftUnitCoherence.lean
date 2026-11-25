/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.CategoryTheory.Scalar.ScalarLeftUnitTransport
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! # The normalized scalar comparison respects the left tensor unit -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale.ExceptionalCoefficients

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh
  Functor.mapDerivedCategoryNatIso

private theorem normalized_left_unit
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    (F : C ⥤ D) [F.Additive] [F.Monoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (r : _root_.DerivedCategory.Q ⋙ S ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)))
    (e : S.obj (𝟙_ _) ≅ 𝟙_ _)
    (ht : TensorNormalizationAux F S r.app δ)
    (hu : UnitNormalizationAux F S r.app e)
    (hrep : ∀ P, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P → IsIso (r.app P))
    (K : _root_.DerivedCategory C) :
    δ.hom.app (𝟙_ _, K) ≫ (e.hom ▷ S.obj K) ≫ (λ_ (S.obj K)).hom =
      S.map (λ_ K).hom := by
  let α := scalarLeftUnitMap S δ e.hom
  let β : tensorLeft (𝟙_ (_root_.DerivedCategory C)) ⋙ S ⟶ S :=
    Functor.whiskerRight (leftUnitorNatIso (_root_.DerivedCategory C)).hom S
  have hδ : ∀ X {Y Z : _root_.DerivedCategory C} (f : Y ⟶ Z),
      S.map (f ▷ X) ≫ δ.hom.app (Z, X) =
        δ.hom.app (Y, X) ≫ (S.map f ▷ S.obj X) := by
    intro X Y Z f
    have h := δ.hom.naturality (show (Y, X) ⟶ (Z, X) from (f, 𝟙 X))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map] at h
    simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id,
      curriedTensor_map_app] using h
  have hab : α = β := by
    apply Localization.natTrans_ext _root_.DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro L
    obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
    have := hπ
    apply (cancel_epi ((tensorLeft (𝟙_ _) ⋙ S).map
      (_root_.DerivedCategory.Q.map π))).1
    rw [α.naturality, β.naturality]
    have := hrep P hP
    have hp := leftUnit_on_representative _root_.DerivedCategory.Q
      _root_.DerivedCategory.Q (F.mapHomologicalComplex (.up ℤ)) S r
      (fun X Y ↦ δ.hom.app (X, Y)) e.hom hδ ht hu P
    exact congrArg (fun z ↦ z ≫ S.map (_root_.DerivedCategory.Q.map π)) hp
  exact NatTrans.congr_app hab K

/-- Left-unit coherence with the site monoidal parameters shared.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-left-unit). -/
def SiteScalarLeftUnitLaw
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type*) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (e : S.obj (𝟙_ _) ≅ 𝟙_ _) : Prop :=
  ∀ K, δ.hom.app (𝟙_ _, K) ≫
    ((derivedTensor D T).map e.hom).app (S.obj K) ≫
      (derivedTensorLeftUnitor D T (S.obj K)).hom =
        S.map (derivedTensorLeftUnitor C T K).hom

/-- Component form of the scalar left-unit normalization, with the site monoidal
structures shared throughout the statement.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-left-unit).
Proof: evaluate the normalization equation at the given derived object. -/
private theorem SiteScalarLeftUnitLaw.component
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type*) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (e : S.obj (𝟙_ _) ≅ 𝟙_ _) (h : SiteScalarLeftUnitLaw C D T S δ e)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C)) :
    δ.hom.app (𝟙_ _, K) ≫
    ((derivedTensor D T).map e.hom).app (S.obj K) ≫
      (derivedTensorLeftUnitor D T (S.obj K)).hom =
        S.map (derivedTensorLeftUnitor C T K).hom := by
  exact h K

private theorem normalized_left_unit_onSite
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type*) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.Monoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : _root_.DerivedCategory.Q ⋙ S ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (e : S.obj (𝟙_ _) ≅ 𝟙_ _)
    (ht : SiteTensorNormalizationAux C D T F S r.app δ)
    (hu : UnitNormalizationAux F S r.app e)
    (hrep : ∀ P, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → IsIso (r.app P)) :
    SiteScalarLeftUnitLaw C D T S δ e := by
  exact normalized_left_unit F S r δ e ht hu hrep

private theorem adjointRepresentative_app_formula
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (QC : C ⥤ V) (QD : D ⥤ W) (FC : C ⥤ D) (UC : D ⥤ C)
    (E : V ⥤ W) (U : W ⥤ V) (adj : E ⊣ U)
    (a : FC ⊣ UC) (fac : UC ⋙ QC ≅ QD ⋙ U) (P : C) :
    (adjointRepresentative QC QD FC UC E U adj a fac).app P =
      (adj.homEquiv _ _).symm (QC.map (a.unit.app P) ≫ fac.hom.app (FC.obj P)) := rfl

private theorem cochain_representative_isIso
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] [HasExactColimitsOfShape ℤ C]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    (F : C ⥤ D) (U : D ⥤ C) [F.Additive] [U.Additive]
    [F.PreservesKFlatQuasiIso] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (ad : S ⊣ U.mapDerivedCategory) (a : F ⊣ U)
    (P : CochainComplex C ℤ) (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso ((adjointRepresentative _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      (F.mapHomologicalComplex (.up ℤ)) (U.mapHomologicalComplex (.up ℤ))
      S U.mapDerivedCategory ad (a.mapHomologicalComplex (.up ℤ))
      U.mapDerivedCategoryFactors.symm).app P) := by
  rw [adjointRepresentative_app_formula]
  exact Adjunction.isIso_cochainTranspose_of_kFlat F U a ad P hP

-- Keep the large ordinary/derived adjunction representative behind one definition.
@[irreducible] private def scalarRepresentativeNatTrans
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    _root_.DerivedCategory.Q ⋙ scalarExtension φ T ⟶
      (ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
        _root_.DerivedCategory.Q :=
  adjointRepresentative _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    ((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ))
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ))
    (scalarExtension φ T) (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory
    (Adjunction.ofIsRightAdjoint _)
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ))
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.symm

private theorem scalarRepresentativeNatTrans_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (scalarRepresentativeNatTrans φ T).app = scalarExtensionRepresentative φ T := by
  funext P
  rw [scalarRepresentativeNatTrans, adjointRepresentative_app_formula]
  unfold scalarExtensionRepresentative
  rw [← mapComplex_unit_formula]
  rfl

private theorem scalarRepresentativeNatTrans_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((scalarRepresentativeNatTrans φ T).app P) := by
  have := extension_preservesKFlatQuasiIso φ T
  unfold scalarRepresentativeNatTrans
  exact cochain_representative_isIso _ _ _ _
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T) P hP

/-- Left unitality of the specified scalar tensor and unit comparisons.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-left-unit).
Proof: tensor the defining representative normalization for the coefficient unit
with the representative at a K-flat complex. The tensor representative normalization,
ordinary scalar left unitality, and localization left unitality imply the equation
after the invertible scalar representative. Cancel that representative. Both sides
are natural transformations on the derived category. Every complex receives a
quasi-isomorphism from a K-flat complex, so localization extensionality and naturality
extend the equation from these representatives to every derived object. -/
theorem tensorIso_left_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u}) :
    SiteScalarLeftUnitLaw (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) T
      (scalarExtension φ T) (tensorIso φ T) (unitIso φ T) := by
  let F := ProEtale.etaleSheafExtendScalars φ T
  let : F.Monoidal := composeAndSheafifyMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  let S := scalarExtension φ T
  let r := scalarRepresentativeNatTrans φ T
  have hr : r.app = scalarExtensionRepresentative φ T := scalarRepresentativeNatTrans_app φ T
  let δ := (tensorIso_existsUnique φ T).choose
  have ht : SiteTensorNormalizationAux (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T F S r.app δ := by
    rw [hr]
    exact (tensorIso_existsUnique φ T).choose_spec.1
  have hu : UnitNormalizationAux F S r.app (unitIso φ T) := by
    rw [hr]
    exact (unitIso_existsUnique φ T).choose_spec.1
  have hrep : ∀ P, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      IsIso (r.app P) := scalarRepresentativeNatTrans_isIso φ T
  have hh := normalized_left_unit_onSite (ModuleCat.{u + 1} A)
    (ModuleCat.{u + 1} B) T F S r δ (unitIso φ T) ht hu hrep
  have heq : tensorIso φ T = δ :=
    eq_of_heq (siteTensorIso_existsUnique φ T).choose_spec.1
  exact heq.symm ▸ hh

end AlgebraicGeometry.Etale.ExceptionalCoefficients
