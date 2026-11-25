/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleOriginScalarData
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleProEtale

/-! # Pullback coordinates for the etale-origin scalar comparison

Source: Stacks Project, Tags 07A4, 0B56 and 0E48. The comparisons below are
constructed from the published coefficient realizations and geometric adjunctions.
(blueprint: def-fix-etale-origin-scalar-pullback-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Etale.scalarTensorIso Scheme.completedAdicDerivedChange

/-- The normalized direct-image comparison for intrinsic realization.
Source: Stacks 00YV and 07A5
(blueprint: def-fix-etale-origin-scalar-pullback-data). -/
def originRealizationPushIso (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (Scheme.sfIntrinsicDerivedEquivalence Z A).functor ⋙ directImageConstantPush A p ≅
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor ⋙
        (Scheme.sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.isoWhiskerLeft _ (properOriginPushIso A p) ≪≫
    Scheme.sfIntrinsicDerivedDirectImageComparison p A

/-- The ambient direct-image mate, including the intrinsic coefficient realization.
Source: Stacks 09A6, 00YV and 07A6
(blueprint: def-fix-etale-origin-scalar-pullback-data). -/
def originMate (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor ⋙
        finiteCoefficientIntrinsicDerivedComparison Y A ⟶
      finiteCoefficientIntrinsicDerivedComparison Z A ⋙ directImageConstantPush A p :=
  Functor.whiskerLeft _ (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Y).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (mateEquiv
        (Etale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
        (derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
        (comparisonOpenDerivedPullbackIso (ULift.{u + 1, u} A) p).inv) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (originRealizationPushIso A p).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Z).inv _

/-- The left mate of the canonical ambient site/direct-image comparison.
Source: Stacks 09A6, 00YV and 07A6
(blueprint: def-fix-etale-origin-scalar-pullback-data). -/
def originPullback (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    finiteCoefficientIntrinsicDerivedComparison Y A ⋙
        Scheme.proEtaleConstantRingDerivedPullback A p ⟶
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).leftDerivedFunctor ⋙
        finiteCoefficientIntrinsicDerivedComparison Z A :=
  ((mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
    (directImageConstantAdjunction A p)).symm
      (TwoSquare.mk _ _ _ _ (originMate A p)))

/-- On bounded-below inputs the ambient mate is the specified included mate.
Source: Stacks 09A6 (blueprint: def-fix-etale-origin-scalar-pullback-data).
Proof: the fixed-coefficient inclusion formula identifies the middle component;
all remaining factors are exactly the intrinsic realization factors. -/
theorem originMate_app
    (A : Type u) [CommRing A] [Finite A] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (originMate A p).app K.obj = (properOriginMateIso A p K).hom := by
  have h := comparison_direct_image_inclusion (ULift.{u + 1, u} A) p K
  simp only [originMate, originRealizationPushIso, properOriginMateIso,
    properOriginFixedMateIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  rw [← h]
  simp only [Functor.map_comp, Category.assoc, asIso_hom]
  rw [← (properOriginPushIso A p).inv.naturality]
  rfl

/-- The counit identity for the canonical site comparison, without a bound on input.
Source: Stacks 07A6 (blueprint: def-fix-etale-origin-scalar-pullback-data).
Proof: this is the inverse mates correspondence's counit identity. -/
theorem originMate_counit
    (A : Type u) [CommRing A] [Finite A] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Z) :
    (Scheme.proEtaleConstantRingDerivedPullback A p).map ((originMate A p).app K) ≫
      (directImageConstantAdjunction A p).counit.app
        ((finiteCoefficientIntrinsicDerivedComparison Z A).obj K) =
    (originPullback A p).app
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj K) ≫
      (finiteCoefficientIntrinsicDerivedComparison Z A).map
        ((Etale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).counit.app K) := by
  exact mateEquiv_counit_symm
    (Etale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
    (directImageConstantAdjunction A p) (TwoSquare.mk _ _ _ _ (originMate A p)) K

/-- Restriction of scalars commutes with geometric pullback, in the direction
used before taking right mates. Source: Stacks 0D6D and 07A6
(blueprint: def-fix-etale-origin-scalar-pullback-data). -/
def originRestrictionPullback
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  (Scheme.proEtaleRingRestrictionDerivedPullback p
    (Scheme.proEtaleConstantRing Y A) (Scheme.proEtaleConstantRing Y B)
    (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing Z B)
    (Scheme.proEtaleConstantRingMap (T := Y) φ)
    (Scheme.proEtaleConstantRingMap (T := Z) φ)
    (Scheme.proEtaleConstantRingComparison p A) (Scheme.proEtaleConstantRingComparison p B)
    (Scheme.proEtaleConstantInverseImageMap_naturality p
      (CommRingCat.ofHom (RingHom.ulift φ))).symm).inv

/-- The scalar extension/restriction pullback map, before taking its right mate.
Source: Stacks 0D6D, 07A6 and 0B56
(blueprint: def-fix-etale-origin-scalar-pullback-data). -/
def originScalarPullback
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (directImageScalarExtension φ Y ⋙ (scalarMateRestriction φ Y).mapDerivedCategory) ⋙
        Scheme.proEtaleConstantRingDerivedPullback A p ⟶
      Scheme.proEtaleConstantRingDerivedPullback A p ⋙
        (directImageScalarExtension φ Z ⋙ (scalarMateRestriction φ Z).mapDerivedCategory) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (originRestrictionPullback φ p) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (directImageScalarPullbackIso φ p).hom _ ≫
    (Functor.associator _ _ _).hom

/-- The etale tensor/pullback comparison with the constant B coefficient.
Source: Stacks 07A4 and 0B56
(blueprint: def-fix-etale-origin-scalar-pullback-data). -/
def originEtaleTensorPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (Etale.derivedTensor (ModuleCat.{u + 1} A) Y).flip.obj (Etale.scalarCoefficient φ Y) ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor ⟶
      (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor ⋙
        (Etale.derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj
          (Etale.scalarCoefficient φ Z) :=
  (Etale.derivedTensorRightCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} A) p (Etale.scalarCoefficient φ Y)).hom ≫
    Functor.whiskerLeft _ ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).flip.map
      (Etale.scalarCoefficientPullbackIso φ p).hom)

/-- The published constant-coefficient tensor comparison as a natural isomorphism.
Source: Stacks 06YY and 00YV
(blueprint: def-fix-etale-origin-scalar-pullback-data). -/
def originTensorComparison
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).flip.obj
        (Etale.scalarCoefficient (RingHom.ulift.{u + 1, u + 1, u, u} φ) T) ⋙
        finiteCoefficientIntrinsicDerivedComparison T A ≅
      finiteCoefficientIntrinsicDerivedComparison T A ⋙
        (directImageScalarExtension φ T ⋙ (scalarMateRestriction φ T).mapDerivedCategory) :=
  Functor.isoWhiskerRight
      (Etale.scalarTensorIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) T).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properOriginRestrictionIso φ T).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.FiniteCompactScalar.siteScalarIso φ T).symm _ ≪≫
    Functor.associator _ _ _

/-- Its component is the existing tensor comparison, with no change of normalization.
Source: the definitions (blueprint: def-fix-etale-origin-scalar-pullback-data).
Proof: expand the two composites; all associators have identity components. -/
theorem originTensorComparison_hom_app
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (C : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :
    (originTensorComparison φ T).hom.app C = (properOriginTensorIso φ T C).hom := by
  simp only [originTensorComparison, properOriginTensorIso, properOriginScalarTensorImage,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.ProEtale
