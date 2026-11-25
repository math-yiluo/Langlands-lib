/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.CategoryTheory.Scalar.ScalarRightUnitTransport
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! # The normalized scalar comparison respects the right tensor unit -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale.ExceptionalCoefficients

private theorem normalized_right_unit
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
    δ.hom.app (K, 𝟙_ _) ≫ (S.obj K ◁ e.hom) ≫ (ρ_ (S.obj K)).hom =
      S.map (ρ_ K).hom := by
  let α := scalarRightUnitMap S δ e.hom
  let β : tensorRight (𝟙_ (_root_.DerivedCategory C)) ⋙ S ⟶ S :=
    Functor.whiskerRight (rightUnitorNatIso (_root_.DerivedCategory C)).hom S
  have hδ : ∀ X {Y Z : _root_.DerivedCategory C} (f : Y ⟶ Z),
      S.map (X ◁ f) ≫ δ.hom.app (X, Z) =
        δ.hom.app (X, Y) ≫ (S.obj X ◁ S.map f) := by
    intro X Y Z f
    have h := δ.hom.naturality (show (X, Y) ⟶ (X, Z) from (𝟙 X, f))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map] at h
    simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      curriedTensor_obj_map] using h
  have hab : α = β := by
    apply Localization.natTrans_ext _root_.DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro L
    obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
    have := hπ
    apply (cancel_epi ((tensorRight (𝟙_ _) ⋙ S).map
      (_root_.DerivedCategory.Q.map π))).1
    rw [α.naturality, β.naturality]
    have := hrep P hP
    have hp := rightUnit_on_representative _root_.DerivedCategory.Q
      _root_.DerivedCategory.Q (F.mapHomologicalComplex (.up ℤ)) S r
      (fun X Y ↦ δ.hom.app (X, Y)) e.hom hδ ht hu P
    exact congrArg (fun z ↦ z ≫ S.map (_root_.DerivedCategory.Q.map π)) hp
  exact NatTrans.congr_app hab K

/-- Right-unit coherence with the site monoidal parameters shared.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-right-unit). -/
def SiteScalarRightUnitLaw
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
  ∀ K, δ.hom.app (K, 𝟙_ _) ≫
    ((derivedTensor D T).obj (S.obj K)).map e.hom ≫
      (derivedTensorRightUnitor D T (S.obj K)).hom =
        S.map (derivedTensorRightUnitor C T K).hom

/-- Component form of the scalar right-unit normalization, with the site monoidal
structures shared throughout the statement.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-right-unit).
Proof: evaluate the normalization equation at the given derived object. -/
private theorem SiteScalarRightUnitLaw.component
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
    (e : S.obj (𝟙_ _) ≅ 𝟙_ _) (h : SiteScalarRightUnitLaw C D T S δ e)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C)) :
    δ.hom.app (K, 𝟙_ _) ≫
    ((derivedTensor D T).obj (S.obj K)).map e.hom ≫
      (derivedTensorRightUnitor D T (S.obj K)).hom =
        S.map (derivedTensorRightUnitor C T K).hom := by
  exact h K

private theorem normalized_right_unit_onSite
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
    SiteScalarRightUnitLaw C D T S δ e := by
  exact normalized_right_unit F S r δ e ht hu hrep

/-- Right unitality of the specified scalar tensor and unit comparisons.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-right-unit).
Proof: tensor the defining representative normalization for the coefficient unit
with the representative at a K-flat complex. The tensor representative normalization,
ordinary scalar right unitality, and localization right unitality imply the equation
after the invertible scalar representative. Cancel that representative. Both sides
are natural transformations on the derived category. Every complex receives a
quasi-isomorphism from a K-flat complex, so localization extensionality and naturality
extend the equation from these representatives to every derived object. -/
theorem tensorIso_right_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u}) :
    SiteScalarRightUnitLaw (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) T
      (scalarExtension φ T) (tensorIso φ T) (unitIso φ T) := by
  let F := ProEtale.etaleSheafExtendScalars φ T
  let : F.Monoidal := composeAndSheafifyMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  have := extension_preservesKFlatQuasiIso φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let S := scalarExtension φ T
  let ad : S ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let r := adjointRepresentative _root_.DerivedCategory.Q
    _root_.DerivedCategory.Q (F.mapHomologicalComplex (.up ℤ))
    (U.mapHomologicalComplex (.up ℤ)) S U.mapDerivedCategory ad
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ))
    U.mapDerivedCategoryFactors.symm
  have hr : r.app = scalarExtensionRepresentative φ T := by
    funext P
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    rfl
  let δ := (tensorIso_existsUnique φ T).choose
  have ht : SiteTensorNormalizationAux (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T F S r.app δ := by
    rw [hr]
    exact (tensorIso_existsUnique φ T).choose_spec.1
  have hu : UnitNormalizationAux F S r.app (unitIso φ T) := by
    rw [hr]
    exact (unitIso_existsUnique φ T).choose_spec.1
  have hrep : ∀ P, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      IsIso (r.app P) := by
    intro P hP
    rw [congrFun hr P]
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    exact Adjunction.isIso_cochainTranspose_of_kFlat _ _
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T) ad P hP
  have hh := normalized_right_unit_onSite (ModuleCat.{u + 1} A)
    (ModuleCat.{u + 1} B) T F S r δ (unitIso φ T) ht hu hrep
  have heq : tensorIso φ T = δ :=
    eq_of_heq (siteTensorIso_existsUnique φ T).choose_spec.1
  exact heq.symm ▸ hh

end AlgebraicGeometry.Etale.ExceptionalCoefficients
