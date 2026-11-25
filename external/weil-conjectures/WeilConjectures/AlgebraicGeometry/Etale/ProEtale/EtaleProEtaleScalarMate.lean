/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarPullbackCube
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarCounitTransposes

/-! # Scalar direct-image mates commute with comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The two canonical B-linear composites transporting the scalar mate agree.
Source: blueprint main-20261015, scalar-six direct-image proof, finite rings paragraph
(blueprint: lem-sfb-etale-proetale-scalar-mate).

Proof, following the node's five steps:
1. Write C for comparison inverse image and l,p,r,s for the etale/pro-etale
   inverse/direct images. Beta is the mate of the inverse-image square d. Hence
   p(beta) followed by the pro-etale counit is d followed by C of the etale counit.
   The qcqs direct-image comparison is invertible on J and on its scalar extension.
2. On flat-term K-flat representatives, the scalar/pullback comparisons c and delta
   are ordinary balancing maps. Both paths through the site/scalar cube send each
   pure tensor to the same pure tensor. The composition and 2-isomorphism coherence
   of lem-sfb-ringed-derived-monoidal-comparisons and the tensor-pullback comparison
   identify these paths on unbounded derived objects, without coefficient flatness.
3. Precompose the desired equation with scalar extension of beta_A. Transpose both
   resulting maps under p_B ⊣ s_B. For the pro-etale path, naturality of c and the
   A-counit equation replace p_A(beta_A) followed by the pro-etale counit by
   d_A followed by C_X of the etale A-counit.
4. Naturality of delta moves that counit past delta_X. The cube equality of step 2
   then rewrites this transpose as C_X of (c_et followed by scalar extension of
   the A-counit), preceded by d_B and p_B(delta_Y). Every map is B-linear.
5. For the other path, the B-counit equation and naturality of d_B give the same
   expression, using the defining transpose of the etale scalar mate. Injectivity
   of the geometric adjunction Hom equivalence gives equality. Precompose with
   scalar extension of beta_A inverse. Neither scalar mate is inverted and the
   intermediate scalar extension on Y need not be bounded below. -/
theorem etaleProEtale_scalar_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hJ : ∃ n : ℤ, J.IsGE n)
    (_hBJ : ∃ n : ℤ, ((pbcFixedScalarExtension X.smallEtaleTopology a).obj J).IsGE n) :
    (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso a f).hom)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J) ≫
      R(lowerStar (ModuleCat.{u + 1} B) f).map ((pbcComparisonReduction X a).hom.app J) =
    (pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).map
        (directImageComparisonAmbientIso A f J hJ).inv ≫
      (pbcComparisonReduction Y a).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
        ((mateEquiv
          (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
          (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
          (TwoSquare.mk _ _ _ _ (scalarPullbackEtaleIso a f).hom)).app J) ≫
      (directImageComparisonAmbient B f).app
        ((pbcFixedScalarExtension X.smallEtaleTopology a).obj J) := by
  have hc := etaleProEtale_scalar_pullback_cube a f
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)
  obtain ⟨hU, hV⟩ := etaleProEtale_scalar_counit_transposes a f J hc
  have hUV : scalarSiteDirectImageU a f J = scalarSiteDirectImageV a f J := by
    apply ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} B) f).homEquiv _ _).symm.injective
    change scalarSiteCounitTranspose a f J (scalarSiteDirectImageU a f J) =
      scalarSiteCounitTranspose a f J (scalarSiteDirectImageV a f J)
    exact hU.trans hV.symm
  have h := congrArg
    (fun q ↦ (pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).map
      (directImageComparisonAmbientIso A f J hJ).inv ≫ q) hUV
  simpa only [scalarSiteDirectImageU, scalarSiteDirectImageV,
    directImageComparisonAmbientIso, asIso_inv, scalarPullbackEtaleIso,
    Etale.scalarMate, Category.assoc, ← Functor.map_comp_assoc,
    IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp] using h

end AlgebraicGeometry.ProEtale

-- Private instance caches of the published import-all interface, kept for its consumers.
section CachedEtaleInstances
open CategoryTheory.Limits
private theorem cachedEtaleGroth (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance
private theorem cachedEtaleSheafify (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance
private theorem cachedEtaleMonoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleCoproducts (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasCountableCoproducts (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleFlatResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasFunctorialFlatResolution (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleInjectiveResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasKInjectiveResolutions (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleExactColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasExactColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleTensor4 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem cachedEtaleTensor12 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensor23 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensorColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).obj V) :=
  inferInstance
private theorem cachedEtaleTensorFlipColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj V) :=
  inferInstance
end CachedEtaleInstances

-- Retain the private import-all interface while sharing its proved implementation.
private alias legacyScalarPullbackEq := AlgebraicGeometry.Etale.scalarPullback_eq
private alias legacyOrdinaryReverseEq := AlgebraicGeometry.Etale.ordinary_reverse_eq
private alias legacyScalarPullbackFromMateEq :=
  AlgebraicGeometry.ProEtale.scalarPullbackEtaleIso_eq_fromMate

namespace AlgebraicGeometry.ProEtale
private def scalarPullbackEtaleIsoFromMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  haveI := (scalarPullbackReverse_isIso a f).2
  (asIso (scalarPullbackReverseEtale a f)).symm
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale
private theorem ordinary_reverse_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ((mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T)).symm
        (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)) =
      (scalarSheafPullbackIso φ f).inv := by
  exact legacyOrdinaryReverseEq φ f

private theorem scalarPullback_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ProEtale.scalarPullbackEtaleIsoFromMate φ f = scalarPullbackIso φ f := by
  exact legacyScalarPullbackEq φ f
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale
private theorem scalarPullbackEtaleIso_eq_fromMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarPullbackEtaleIso a f = scalarPullbackEtaleIsoFromMate a f := by
  exact legacyScalarPullbackFromMateEq a f
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale
-- Preserve the private representative equation used by import-all consumers.
private theorem geometric_rep_eq {A : Type (u + 1)} [CommRing A]
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat A)) ℤ) :
    scalarGeometricRepresentative A f P =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        (DerivedCategory.Q.obj P) ≫
      (upperStar (ModuleCat A) f).mapDerivedCategoryFactors.hom.app P := by
  exact scalarGeometricRepresentative_eq A f P
end AlgebraicGeometry.Etale
