/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # Existence of the normalized derived scalar/pullback comparison

## References

* Stacks Project, Tags 07A4, 0G7E and 07A7
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem mapComplex_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem extension_preservesKFlatQuasiIso {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).PreservesKFlatQuasiIso := by
  classical
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let adj : E ⊣ U :=
    Sheaf.adjunction X.smallEtaleTopology (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u +
      1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let coeff := (Functor.const X.Etaleᵒᵖ).obj B
  let a := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u
    + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj coeff) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} S))
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso coeff).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj coeff))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj coeff)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have hE : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj coeff)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  exact hE

private theorem derivedRepresentative_isIso
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((ad.homEquiv _ _).symm
      (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P))) := by
  rw [← mapComplex_unit_formula]
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  rw [← Adjunction.leftDerivedCochainCounit E U adj ad P]
  infer_instance

private def adjointTranspose
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (F : C ⥤ E) {S : D ⥤ E} {U : E ⥤ D}
    (ad : S ⊣ U) (θ : Q ⟶ F ⋙ U) : Q ⋙ S ⟶ F where
  app X := (ad.homEquiv _ _).symm (θ.app X)
  naturality X Y a := ad.homEquiv_naturality_right_square (Q.map a)
    (θ.app Y) (θ.app X) (F.map a)
    (by simpa only [Functor.comp_map] using θ.naturality a)

private theorem adjointComparison_naturality
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (Q : C ⥤ A) (Q' : D ⥤ B) (F : C ⥤ D) (G : D ⥤ C)
    {S : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ G) (ad : S ⊣ U)
    (e : G ⋙ Q ≅ Q' ⋙ U) {P P' : C} (a : P ⟶ P') :
    S.map (Q.map a) ≫ (ad.homEquiv _ _).symm
        (Q.map (adj.unit.app P') ≫ e.hom.app (F.obj P')) =
      (ad.homEquiv _ _).symm (Q.map (adj.unit.app P) ≫ e.hom.app (F.obj P)) ≫
        Q'.map (F.map a) := by
  let θ : Q ⟶ F ⋙ Q' ⋙ U :=
    (Functor.leftUnitor Q).inv ≫ Functor.whiskerRight adj.unit Q ≫
      Functor.whiskerLeft F e.hom
  have h := (adjointTranspose Q (F ⋙ Q') ad θ).naturality a
  simp only [adjointTranspose, θ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Functor.comp_map,
    Functor.comp_obj, Functor.id_obj, Category.id_comp] at h ⊢
  exact h

private theorem cochainAdjointComparison_naturality
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) {P P' : CochainComplex C ℤ} (a : P ⟶ P') :
    L.map (_root_.DerivedCategory.Q.map a) ≫ (ad.homEquiv _ _).symm
        (_root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P' ≫
            (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P' ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P') ≫
          U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P')) =
      (ad.homEquiv _ _).symm
        (_root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
            (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
          U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        _root_.DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map a) := by
  simp only [← mapComplex_unit_formula]
  exact adjointComparison_naturality _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    (E.mapHomologicalComplex (.up ℤ)) (U.mapHomologicalComplex (.up ℤ))
    (adj.mapHomologicalComplex (.up ℤ)) ad U.mapDerivedCategoryFactors.symm a

private def cochainAdjointComparison
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) :
    _root_.DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q where
  app P := (ad.homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
      U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P))
  naturality _ _ a := cochainAdjointComparison_naturality E U adj ad a

private theorem cochainAdjointComparison_isIso
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((cochainAdjointComparison E U adj ad).app P) :=
  derivedRepresentative_isIso E U adj ad P hP

private def withComponents
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) (r : ∀ X, F.obj X ⟶ G.obj X) (h : ∀ X, α.app X = r X) : F ⟶ G where
  app := r
  naturality X Y f := by
    rw [← h X, ← h Y]
    exact α.naturality f

private def scalarRepresentativeTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    _root_.DerivedCategory.Q ⋙ scalarExtension φ X ⟶
      (ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ) ⋙
        _root_.DerivedCategory.Q :=
  withComponents
    (cochainAdjointComparison (ProEtale.etaleSheafExtendScalars φ X)
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (ProEtale.etaleSheafExtendScalarsAdjunction φ X) (L := scalarExtension φ X)
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)))
    (scalarExtensionRepresentative φ X) (fun _ ↦ rfl)

private theorem scalarRepresentativeTransformation_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((scalarRepresentativeTransformation φ X).app P) := by
  let E := ProEtale.etaleSheafExtendScalars φ X
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ X
  exact cochainAdjointComparison_isIso E U
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X) (L := scalarExtension φ X)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)) P hP

private def derivedCochainCounit
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] :
    _root_.DerivedCategory.Q ⋙ F.leftDerivedFunctor ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q :=
  Functor.whiskerRight (_root_.DerivedCategory.quotientCompQhIso _).inv F.leftDerivedFunctor ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) F.leftDerivedFunctorCounit ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom _root_.DerivedCategory.Qh ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (_root_.DerivedCategory.quotientCompQhIso _).hom

private theorem derivedCochainCounit_isIso
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : CochainComplex C ℤ) :
    IsIso ((derivedCochainCounit F).app P) := by
  dsimp only [derivedCochainCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

private def geometricRepresentativeTransformation
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X) :
    _root_.DerivedCategory.Q ⋙ L(upperStar (ModuleCat.{u + 1} A) f) ⟶
      (upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ) ⋙
        _root_.DerivedCategory.Q :=
  withComponents (derivedCochainCounit (upperStar (ModuleCat.{u + 1} A) f))
    (scalarGeometricRepresentative A f) (fun _ ↦ rfl)

private theorem geometricRepresentativeTransformation_isIso
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    IsIso ((geometricRepresentativeTransformation A f).app P) :=
  derivedCochainCounit_isIso (upperStar (ModuleCat.{u + 1} A) f) P

private theorem normalizedComparison_of_resolution
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (F G : D ⥤ E) (H : C ⥤ E) (s : Q ⋙ G ⟶ H) (t : Q ⋙ F ⟶ H)
    (R : C ⥤ C) (π : R ⟶ 𝟭 C)
    (hπ : ∀ X, IsIso (Q.map (π.app X)))
    (hs : ∀ X, IsIso (s.app (R.obj X)))
    (ht : ∀ X, IsIso (t.app (R.obj X))) :
    ∃ c : F ≅ G, ∀ X, c.hom.app (Q.obj X) ≫ s.app X = t.app X := by
  let : ∀ X, IsIso (Q.map (π.app X)) := hπ
  let : ∀ X, IsIso (s.app (R.obj X)) := hs
  let : ∀ X, IsIso (t.app (R.obj X)) := ht
  have : IsIso (Functor.whiskerRight π (Q ⋙ F)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    dsimp only [Functor.whiskerRight_app, Functor.comp_map]
    infer_instance
  have : IsIso (Functor.whiskerRight π (Q ⋙ G)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    dsimp only [Functor.whiskerRight_app, Functor.comp_map]
    infer_instance
  have : IsIso (Functor.whiskerLeft R s) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    exact hs X
  have : IsIso (Functor.whiskerLeft R t) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro X
    exact ht X
  let e : Q ⋙ F ≅ Q ⋙ G :=
    (asIso (Functor.whiskerRight π (Q ⋙ F))).symm ≪≫
      asIso (Functor.whiskerLeft R t) ≪≫
      (asIso (Functor.whiskerLeft R s)).symm ≪≫
      asIso (Functor.whiskerRight π (Q ⋙ G))
  refine ⟨Localization.liftNatIso Q W (Q ⋙ F) (Q ⋙ G) F G e, ?_⟩
  intro X
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 _ ≫ e.hom.app X ≫ 𝟙 _) ≫ s.app X = t.app X
  simp only [Category.id_comp, Category.comp_id]
  simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    asIso_hom, asIso_inv, NatIso.isIso_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Category.assoc]
  have hsN := s.naturality (π.app X)
  have htN := t.naturality (π.app X)
  dsimp only [Functor.comp_map, Functor.id_obj] at hsN htN
  rw [hsN]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← htN]
  simp

attribute [local irreducible] scalarRepresentativeTransformation
  geometricRepresentativeTransformation cochainAdjointComparison derivedCochainCounit withComponents

attribute [local irreducible] ProEtale.pbcFixedScalarExtension
  scalarSheafPullbackComplexIso scalarSheafPullbackIso
  scalarExtensionRepresentative scalarGeometricRepresentative
  Functor.leftAdjoint Functor.rightAdjoint Functor.mapDerivedCategory upperStar lowerStar

/-- The normalized derived scalar/pullback comparison exists. -/
theorem scalarPullbackIso_exists
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    ∃ c : scalarExtension φ W ⋙ L(upperStar (ModuleCat.{u + 1} B) f) ≅
        L(upperStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ Z,
      ∀ (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      c.hom.app (_root_.DerivedCategory.Q.obj P) ≫
          (scalarExtension φ Z).map (scalarGeometricRepresentative A f P) ≫
          scalarExtensionRepresentative φ Z
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
        L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ W P) ≫
          scalarGeometricRepresentative B f
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).hom.app P) := by
  classical
  let FA := upperStar (ModuleCat.{u + 1} A) f
  let FB := upperStar (ModuleCat.{u + 1} B) f
  let EW := ProEtale.etaleSheafExtendScalars φ W
  let EZ := ProEtale.etaleSheafExtendScalars φ Z
  let F := scalarExtension φ W ⋙ FB.leftDerivedFunctor
  let G := FA.leftDerivedFunctor ⋙ scalarExtension φ Z
  let H := FA.mapHomologicalComplex (.up ℤ) ⋙ EZ.mapHomologicalComplex (.up ℤ) ⋙
    _root_.DerivedCategory.Q
  let rW := scalarRepresentativeTransformation φ W
  let rZ := scalarRepresentativeTransformation φ Z
  let gA := geometricRepresentativeTransformation A f
  let gB := geometricRepresentativeTransformation B f
  let s : _root_.DerivedCategory.Q ⋙ G ⟶ H :=
    Functor.whiskerRight gA (scalarExtension φ Z) ≫
      Functor.whiskerLeft (FA.mapHomologicalComplex (.up ℤ)) rZ
  let t : _root_.DerivedCategory.Q ⋙ F ⟶ H :=
    Functor.whiskerRight rW FB.leftDerivedFunctor ≫
      Functor.whiskerLeft (EW.mapHomologicalComplex (.up ℤ)) gB ≫
      Functor.whiskerRight (scalarSheafPullbackComplexIso φ f).hom _root_.DerivedCategory.Q
  let C := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  have hπ : ∀ K, IsIso (_root_.DerivedCategory.Q.map
      (Λ.reduced.resolutionNatTrans.app K)) := fun K ↦ inferInstance
  have hs : ∀ K, IsIso (s.app (Λ.reduced.resolutionFunctor.obj K)) := by
    intro K
    have hF := FA.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le K
    have := scalarRepresentativeTransformation_isIso φ Z _ hF
    have := geometricRepresentativeTransformation_isIso A f
      (Λ.reduced.resolutionFunctor.obj K)
    dsimp only [s, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have ht : ∀ K, IsIso (t.app (Λ.reduced.resolutionFunctor.obj K)) := by
    intro K
    have hP := Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
    have := scalarRepresentativeTransformation_isIso φ W _ hP
    have := geometricRepresentativeTransformation_isIso B f
      ((EW.mapHomologicalComplex (.up ℤ)).obj (Λ.reduced.resolutionFunctor.obj K))
    dsimp only [t, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  obtain ⟨c, hc⟩ := normalizedComparison_of_resolution _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) F G H s t
    Λ.reduced.resolutionFunctor Λ.reduced.resolutionNatTrans hπ hs ht
  refine ⟨c, ?_⟩
  intro P _hP
  have h := hc P
  dsimp only [s, t, rW, rZ, gA, gB, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj] at h
  delta scalarRepresentativeTransformation geometricRepresentativeTransformation withComponents at h
  dsimp only [F, G, H, FA, FB, EW, EZ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj] at h
  exact h

end AlgebraicGeometry.Etale
