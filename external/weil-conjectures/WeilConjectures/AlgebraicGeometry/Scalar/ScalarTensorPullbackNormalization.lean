/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarTensorRepresentativePullback
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSheafTensorPullbackComplex
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarRestrictionGeometricRepresentative
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData

/-!
# Tensor normalization of a scalar/pullback comparison

## References

* Stacks Project, Tags 07A4, 0G7E and 07A7
* Tag 0GL6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Keep derived functors and chosen adjoints abstract while elaborating the diagrams.
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension upperStar lowerStar

private theorem geometric_isIso
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    IsIso (scalarGeometricRepresentative A f P) := by
  rw [scalarGeometricRepresentative_eq]
  infer_instance

attribute [local irreducible] scalarTensorIso scalarGeometricRepresentative
  scalarExtensionRepresentative scalarTensorRepresentative

/-- Forgetting the coefficients in a representative-normalized scalar/pullback
comparison gives the specified monoidal pullback comparison, with the coefficient
object identified by exact inverse image and its monoidal unit. -/
theorem scalarTensorPullback_normalization_kFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (c : L(upperStar (ModuleCat.{u + 1} B) f).obj
        ((scalarExtension φ W).obj (_root_.DerivedCategory.Q.obj P)) ⟶
      (scalarExtension φ Z).obj
        (L(upperStar (ModuleCat.{u + 1} A) f).obj (_root_.DerivedCategory.Q.obj P)))
    (hc : c ≫ (scalarExtension φ Z).map (scalarGeometricRepresentative A f P) ≫
          scalarExtensionRepresentative φ Z
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
        L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ W P) ≫
          scalarGeometricRepresentative B f
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).hom.app P)) :
    let C := _root_.DerivedCategory.Q.obj P
    (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ W).obj C) ≫
        (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map c ≫
        (scalarTensorIso φ Z).hom.app (L(upperStar (ModuleCat.{u + 1} A) f).obj C) =
      L(upperStar (ModuleCat.{u + 1} A) f).map ((scalarTensorIso φ W).hom.app C) ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app C).app
          (scalarCoefficient φ W) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          (L(upperStar (ModuleCat.{u + 1} A) f).obj C)).map
          (scalarCoefficientPullbackIso φ f).hom := by
  let FA := L(upperStar (ModuleCat.{u + 1} A) f)
  let UZ := Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ
  let PA := ((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P
  let EP := ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P
  let MW := scalarCoefficientSheaf φ W
  let MZ := scalarCoefficientSheaf φ Z
  let TZ := (derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj (scalarCoefficient φ Z)
  let qW := scalarTensorRepresentative φ W P
  let qZ := scalarTensorRepresentative φ Z PA
  let bZ := DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex (scalarSheafTensorTransformation φ Z) (.up ℤ)).app PA)
  let a := scalarGeometricRepresentative A f P
  let d := ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
      (DerivedCategory.Q.obj P)).app (scalarCoefficient φ W) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
      (FA.obj (DerivedCategory.Q.obj P))).map (scalarCoefficientPullbackIso φ f).hom
  let t := DerivedCategory.Q.map
    ((Functor.mapHomologicalComplexCompIso
        (upperStarTensorSingleIso A f (scalarCoefficientSheafPullbackIso φ f)) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl
        (upperStar (ModuleCat.{u + 1} A) f ⋙ tensorRight MZ)) (.up ℤ)).symm).hom.app P)
  have ht : d ≫ TZ.map a ≫ qZ = FA.map qW ≫
      scalarGeometricRepresentative A f
        (((tensorRight MW).mapHomologicalComplex (.up ℤ)).obj P) ≫ t := by
    simpa only [d, Category.assoc] using scalarTensorRepresentative_pullback φ f P
  have : IsIso a := geometric_isIso A f P
  have : IsIso qW := scalarTensorRepresentative_isIso φ W P _hP
  have : IsIso t := by dsimp only [t]; infer_instance
  have : IsIso d := by dsimp only [d]; infer_instance
  have : IsIso (scalarGeometricRepresentative A f
      (((tensorRight MW).mapHomologicalComplex (.up ℤ)).obj P)) := geometric_isIso _ _ _
  have : IsIso (d ≫ TZ.map a ≫ qZ) := by rw [ht]; infer_instance
  have : IsIso (TZ.map a ≫ qZ) := IsIso.of_isIso_comp_left d _
  have : IsIso qZ := IsIso.of_isIso_comp_left (TZ.map a) _
  have hbal (T : Scheme.{u}) : IsIso (scalarSheafTensorTransformation φ T) := by
    have (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
        IsIso ((scalarSheafTensorTransformation φ T).app M) := scalarSheafTensorMap_isIso φ T M
    exact NatIso.isIso_of_isIso_app _
  have : IsIso bZ := by
    have := hbal Z
    have : IsIso ((NatTrans.mapHomologicalComplex (scalarSheafTensorTransformation φ Z)
        (.up ℤ)).app PA) :=
      ((NatIso.mapHomologicalComplex (asIso (scalarSheafTensorTransformation φ Z))
        (.up ℤ)).app PA).isIso_hom
    dsimp only [bZ]
    infer_instance
  let post := TZ.map a ≫ qZ ≫ bZ
  have : IsIso post := by dsimp only [post]; infer_instance
  apply (cancel_mono post).1
  have hz := scalarTensorIso_representative φ Z PA
  have hw := scalarTensorIso_representative φ W P
  have hn := (scalarTensorIso φ Z).hom.naturality a
  have hr := scalarRestrictionPullbackIso_geometric_representative φ f EP
  have hres := (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryFactors.hom
    |>.naturality ((scalarSheafPullbackComplexIso φ f).hom.app P)
  have hs := congrArg DerivedCategory.Q.map (scalarSheafTensorPullbackComplex_square φ f P)
  simp only [DerivedCategory.Q.map_comp] at hs
  change (_ ≫ UZ.map c ≫
      (scalarTensorIso φ Z).hom.app (FA.obj (DerivedCategory.Q.obj P))) ≫
      (TZ.map a ≫ qZ ≫ bZ) =
    (FA.map ((scalarTensorIso φ W).hom.app (DerivedCategory.Q.obj P)) ≫ d) ≫
      (TZ.map a ≫ qZ ≫ bZ)
  dsimp only [UZ, FA]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  rw [hz]
  simp only [← Functor.map_comp_assoc]
  erw [hc]
  simp only [Functor.map_comp, Category.assoc]
  erw [hres]
  rw [← reassoc_of% ((scalarRestrictionPullbackIso φ f).hom.naturality
    (scalarExtensionRepresentative φ W P))]
  erw [reassoc_of% hr]
  simp only [← Functor.map_comp_assoc]
  erw [← hw]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (scalarGeometricRepresentative_naturality A f
    ((NatTrans.mapHomologicalComplex (scalarSheafTensorTransformation φ W) (.up ℤ)).app P))]
  simp only [Functor.comp_map]
  erw [hs]
  erw [← reassoc_of% ht]

end AlgebraicGeometry.Etale
