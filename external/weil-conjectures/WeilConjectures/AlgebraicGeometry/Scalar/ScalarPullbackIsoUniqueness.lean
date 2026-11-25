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

/-! Uniqueness of the normalized derived scalar/pullback comparison.

## References

* Stacks 07A4, 0G7E and 07A7
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

private theorem scalarRepresentative_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (scalarExtensionRepresentative φ X P) := by
  let E := ProEtale.etaleSheafExtendScalars φ X
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ X
  exact derivedRepresentative_isIso E U (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (L := scalarExtension φ X)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)) P hP

/-- Two normalized scalar/pullback isomorphisms coincide. -/
theorem scalarPullbackIso_unique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    {c d : scalarExtension φ W ⋙ L(upperStar (ModuleCat.{u + 1} B) f) ≅
        L(upperStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ Z}
    (hc : ∀ (P : CochainComplex
        (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      c.hom.app (_root_.DerivedCategory.Q.obj P) ≫
          (scalarExtension φ Z).map (scalarGeometricRepresentative A f P) ≫
          scalarExtensionRepresentative φ Z
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
        L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ W P) ≫
          scalarGeometricRepresentative B f
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).hom.app P))
    (hd : ∀ (P : CochainComplex
        (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      d.hom.app (_root_.DerivedCategory.Q.obj P) ≫
          (scalarExtension φ Z).map (scalarGeometricRepresentative A f P) ≫
          scalarExtensionRepresentative φ Z
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
        L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ W P) ≫
          scalarGeometricRepresentative B f
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).hom.app P)) :
    c = d := by
  apply Iso.ext
  apply Localization.natTrans_ext _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  classical
  let C := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  let P := Λ.reduced.resolutionFunctor.obj K
  let π : P ⟶ K := Λ.reduced.resolutionNatTrans.app K
  have hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P :=
    Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
  have hF : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) :=
    (upperStar (ModuleCat.{u + 1} A) f).kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj
      Λ.reduced ObjectProperty.flat.essImage_ι_le K
  have : IsIso (scalarExtensionRepresentative φ Z
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P)) :=
    scalarRepresentative_isIso φ Z _ hF
  have : IsIso (scalarGeometricRepresentative A f P) := by
    unfold scalarGeometricRepresentative
    infer_instance
  have heq : c.hom.app (_root_.DerivedCategory.Q.obj P) =
      d.hom.app (_root_.DerivedCategory.Q.obj P) := by
    apply (cancel_mono ((scalarExtension φ Z).map (scalarGeometricRepresentative A f P))).1
    apply (cancel_mono (scalarExtensionRepresentative φ Z
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P))).1
    simpa only [Category.assoc] using (hc P hP).trans (hd P hP).symm
  have : QuasiIso π := inferInstance
  apply (cancel_epi ((scalarExtension φ W ⋙
    L(upperStar (ModuleCat.{u + 1} B) f)).map (_root_.DerivedCategory.Q.map π))).1
  rw [c.hom.naturality, d.hom.naturality, heq]

end AlgebraicGeometry.Etale
