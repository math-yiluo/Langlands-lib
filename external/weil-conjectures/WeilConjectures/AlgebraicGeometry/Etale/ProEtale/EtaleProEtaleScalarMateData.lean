/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Derived.DerivedScalarRestrictionPullbackMate
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
import all WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor

/-!
# Scalar mates commute with the etale/pro-etale comparison

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-direct-image.proof.md, finite rings paragraph
(blueprint: lem-sfb-etale-proetale-scalar-mate).

This module contains the item statement and the canonical scalar and direct-image
comparison helpers it uses. The helpers are specialized interfaces for the
recorded tensor-pullback and direct-image comparison nodes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.Functor
private theorem counitIsoOnImage
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) (X : C) [IsIso (a.unit.app X)] {Y : D} (e : Y ≅ F.obj X) :
    IsIso (a.counit.app Y) := by
  have : IsIso (a.counit.app (F.obj X)) := by
    have h := a.left_triangle_components X
    have : IsIso (F.map (a.unit.app X) ≫ a.counit.app (F.obj X)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (F.map (a.unit.app X)) _
  have h := a.counit.naturality e.hom
  simp only [Functor.id_map] at h
  have : IsIso (a.counit.app Y ≫ e.hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

namespace AlgebraicGeometry.ProEtale

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the reverse scalar/pullback
comparison is the inverse scalar-adjunction mate of the exact pro-etale
restriction/pullback square. It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackReverseProEtale
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) a ⟶
      pbcFixedScalarExtension (Scheme.ProEt.topology Y) a ⋙
        L(upperStar (ModuleCat.{u + 1} B) f) :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a))).symm
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom))

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the reverse comparison
on the etale site uses the actual exact restriction/pullback square. It specializes
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Source: Stacks 07A4
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackReverseEtale
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a ⟶
      pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology a))).symm
    (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom))

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the canonical tensor/pullback
comparison is invertible for arbitrary ring maps. This is the constant-coefficient
specialization of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Source: Stacks 07A4 and 0G7E (blueprint: lem-sfb-scalar-site-comparison-normalized-data).
Proof: choose K-flat resolutions with flat terms on either small site. Exact
inverse image preserves these resolutions and commutes with constant-ring scalar
extension. On the representatives the inverse scalar mate is the ordinary
balancing map, since its scalar-unit equation is the ordinary tensor adjunction.
Its inverse is the opposite balancing identification. The pure-tensor and unit
normalizations of the general recorded tensor-pullback comparison identify these
maps with its constant-coefficient specialization. Naturality and localization
extend them to all derived objects, preserving both inverse equations. This proves
invertibility on both sites without flatness of B over A or boundedness. -/
theorem scalarPullbackReverse_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarPullbackReverseProEtale a f) ∧
      IsIso (scalarPullbackReverseEtale a f) := by
  exact ⟨proEtaleScalarPullbackMate_isIso a f, etaleScalarPullbackMate_isIso a f⟩

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the specified forward
pro-etale tensor/pullback isomorphism is the inverse of the actual scalar mate.
It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and is not arbitrary.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackProEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension (Scheme.ProEt.topology Y) a ⋙
        L(upperStar (ModuleCat.{u + 1} B) f) ≅
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) a :=
  haveI := (scalarPullbackReverse_isIso a f).1
  (asIso (scalarPullbackReverseProEtale a f)).symm

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the specified forward
etale tensor/pullback isomorphism is the inverse of the actual scalar mate.
It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
It reuses the published `AlgebraicGeometry.Etale.scalarPullbackIso`.
The proved private comparison at the end of this file identifies this abbreviation
with the original inverse-mate expression, preserving its canonical normalization.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
abbrev scalarPullbackEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  Etale.scalarPullbackIso a f

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the canonical inverse-image
square identifies exact termwise inverse images with their left derived functors.
It specializes `theorem-comparison-direct-images`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbientPullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the ambient site/direct-image
comparison is the actual counit mate of the specified inverse-image square.
It specializes `theorem-comparison-direct-images`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbient
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R(Etale.lowerStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f) :=
  (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (directImageComparisonAmbientPullbackIso A f).hom))

section AmbientComparisonProof
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.leftAdjoint Functor.rightAdjoint

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the ambient canonical
comparison is invertible at every bounded-below input. It specializes
`theorem-comparison-direct-images`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate).
Proof: the site square is the canonical fibre-product square (step 1). Exact inverse
images preserve lower bounds, and termwise localization constructs the displayed square
(step 2). Its derived mate is beta, with the prescribed counit equation (step 3).
For qcqs f, the existing direct-image comparison gives an isomorphism e between the
endpoints. Full faithfulness of comparison inverse image identifies both Hom sets
out of a comparison image with the same etale adjunction Hom set. By the mate formula,
postcomposition with beta is the identity under these identifications. Surjectivity
and injectivity give a two-sided inverse for beta (step 4). The derived classical
equivalence then transports classical bounded-below inputs and all-degree cohomology
continuity across this isomorphism (step 5). Naturality and the triangle
identities identify the ambient mate on D+ with the previously recorded comparison,
including its units, counits, identity and composition normalization (step 6).
No finiteness of A is used in this discrete-coefficient theorem. -/
theorem directImageComparisonAmbient_isIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hJ : ∃ n : ℤ, J.IsGE n) :
    IsIso ((directImageComparisonAmbient A f).app J) := by
  have hplus : DerivedCategory.TStructure.t.plus J := _hJ
  have hr := Etale.plus_rightDerivedLowerStar_obj (ModuleCat.{u + 1} A) f hplus
  have hx := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) X J hplus
  have hy := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) Y
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) hr
  let e := (rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} A) f).app ⟨J, hplus⟩
  have hs : IsIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app
      (R(lowerStar (ModuleCat.{u + 1} A) f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J))) :=
    counitIsoOnImage (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y)
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) e
  exact Adjunction.isIso_mateEquiv_app_of_isIso
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (directImageComparisonAmbientPullbackIso A f)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) X) J

end AmbientComparisonProof

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the inverse of beta is
taken only at the specified bounded-below input. It specializes
`theorem-comparison-direct-images`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbientIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hJ : ∃ n : ℤ, J.IsGE n) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) ≅
      R(lowerStar (ModuleCat.{u + 1} A) f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J) :=
  haveI := directImageComparisonAmbient_isIso A f J hJ
  asIso ((directImageComparisonAmbient A f).app J)

end AlgebraicGeometry.ProEtale

open scoped CategoryTheory.Functor

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

section CanonicalScalarPullbackIdentification

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctorCounit Functor.rightDerivedFunctorUnit
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.leftAdjoint Functor.rightAdjoint

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh
  Functor.mapDerivedCategoryNatIso

private theorem inverse_normalization
    {C : Type*} [Category C] {U V W Z : C} (e : U ≅ V)
    (a : V ⟶ W) (b : U ⟶ Z) (c : Z ≅ W)
    (h : e.hom ≫ a = b ≫ c.hom) : e.inv ≫ b = a ≫ c.inv := by
  apply (cancel_mono c.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem ordinary_reverse_of_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {sx : A ⥤ B} {rx : B ⥤ A} (ax : sx ⊣ rx)
    {st : C ⥤ D} {rt : D ⥤ C} (at' : st ⊣ rt)
    {f : A ⥤ C} {rf : C ⥤ A} (af : f ⊣ rf)
    {g : B ⥤ D} {rg : D ⥤ B} (ag : g ⊣ rg)
    (e : rx ⋙ f ≅ g ⋙ rt) (δ : rg ⋙ rx ≅ rt ⋙ rf)
    (hδ : (mateEquiv ag af (TwoSquare.mk _ _ _ _ e.hom)) = δ.hom) :
    ((mateEquiv ax at').symm (TwoSquare.mk _ _ _ _ e.hom)) =
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv := by
  apply (mateEquiv ax at').injective
  apply (mateEquiv ag af).injective
  rw [Equiv.apply_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  have h := iterated_mateEquiv_conjugateEquiv ax at' af ag
    (TwoSquare.mk _ _ _ _
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv)
  dsimp only [TwoSquare.mk] at h hδ
  rw [h, hδ]
  simp only [conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  erw [Equiv.apply_symm_apply]

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar
attribute [-instance] ProEtale.pbcRestriction_isRightAdjoint
private theorem scalarRightAdjoint {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).IsRightAdjoint :=
  ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology φ
attribute [local instance] scalarRightAdjoint

private theorem ordinary_reverse_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ((mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T)).symm
        (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)) =
      (scalarSheafPullbackIso φ f).inv := by
  unfold scalarSheafPullbackIso
  exact ordinary_reverse_of_mate
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarRestrictScalarsIsoSheaf φ f) (lowerStarCompRestrictScalarsIso φ f)
    (underived_mate φ f)

private def scalarCochainUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    P ⟶ ((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P :=
  scalarRepresentativeUnit φ T P

attribute [local irreducible] scalarExtensionRepresentative scalarGeometricRepresentative
  scalarRestrictionPullbackIso ProEtale.scalarPullbackReverseEtale

private theorem scalar_rep_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app
        (_root_.DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        (scalarExtensionRepresentative φ T P) =
    _root_.DerivedCategory.Q.map
      (scalarCochainUnit φ T P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact scalarExtensionRepresentative_unit_public φ T P

private theorem scalar_complex_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map
      (scalarCochainUnit φ X P) ≫
      ((Functor.mapHomologicalComplexCompIso (upperStarRestrictScalarsIsoSheaf φ f) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (upperStar (ModuleCat.{u + 1} B) f ⋙
            Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).symm).hom.app
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P)) =
    scalarCochainUnit φ T
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).map
        ((scalarSheafPullbackComplexIso φ f).inv.app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  change (upperStar (ModuleCat.{u + 1} A) f).map
      (𝟙 _ ≫ (ProEtale.etaleSheafExtendScalarsAdjunction φ X).unit.app (P.X i) ≫ 𝟙 _) ≫
      ((upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((ProEtale.etaleSheafExtendScalars φ X).obj (P.X i)) ≫ 𝟙 _) =
    (𝟙 _ ≫ (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app
      ((upperStar (ModuleCat.{u + 1} A) f).obj (P.X i)) ≫ 𝟙 _) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        (𝟙 _ ≫ (scalarSheafPullbackIso φ f).inv.app (P.X i))
  simp only [Category.id_comp, Category.comp_id]
  let M := P.X i
  have h := unit_mateEquiv_symm
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom) M
  change (upperStar (ModuleCat.{u + 1} A) f).map
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).unit.app M) ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((ProEtale.etaleSheafExtendScalars φ X).obj M) =
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app
      ((upperStar (ModuleCat.{u + 1} A) f).obj M) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        (((mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
          (ProEtale.etaleSheafExtendScalarsAdjunction φ T)).symm
          (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).app M) at h
  rw [ordinary_reverse_eq] at h
  exact h

private theorem normalized_scalar_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {sx : C ⥤ D} {rx : D ⥤ C} {st : E ⥤ F} {rt : F ⥤ E}
    (ax : sx ⊣ rx) (at' : st ⊣ rt) (f : C ⥤ E) (g : D ⥤ F)
    (e : rx ⋙ f ⟶ g ⋙ rt) (P : C) (Q : D) (V : E) (W Z : F)
    (u : sx.obj P ⟶ Q) (v : st.obj V ⟶ W)
    (a : f.obj P ⟶ V) (b : g.obj Q ⟶ Z) (c : W ⟶ Z)
    (q : P ⟶ rx.obj Q) (t : V ⟶ rt.obj W)
    (hq : ax.unit.app P ≫ rx.map u = q)
    (ht : at'.unit.app V ≫ rt.map v = t)
    (h : f.map q ≫ e.app Q ≫ rt.map b = a ≫ t ≫ rt.map c) :
    ((mateEquiv ax at').symm (TwoSquare.mk _ _ _ _ e)).app P ≫
        g.map u ≫ b = st.map a ≫ v ≫ c := by
  apply (at'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← reassoc_of% (unit_mateEquiv_symm ax at'
    (TwoSquare.mk _ _ _ _ e) P)]
  erw [← e.naturality_assoc]
  simp only [Functor.comp_map, ← f.map_comp_assoc]
  rw [hq]
  erw [← at'.unit.naturality_assoc]
  simp only [Functor.id_map]
  rw [reassoc_of% ht]
  exact h

private theorem representative_square_unit
    {C₀ E₀ C E F : Type*}
    [Category C₀] [Category E₀] [Category C] [Category E] [Category F]
    (Q : C₀ ⥤ C) (QT : E₀ ⥤ E) (f₀ : C₀ ⥤ E₀) (f : C ⥤ E) (rt : F ⥤ E)
    {P N : C₀} {V W : E₀} {Z : C} {H : E} {Y Y' : F}
    (q : P ⟶ N) (t : f₀.obj P ⟶ V) (e₀ : f₀.obj N ⟶ W) (c₀ : V ⟶ W)
    (rX : Q.obj N ⟶ Z) (e : f.obj Z ⟶ H) (b : H ⟶ rt.obj Y')
    (aP : f.obj (Q.obj P) ⟶ QT.obj (f₀.obj P))
    (aN : f.obj (Q.obj N) ⟶ QT.obj (f₀.obj N))
    (rT : QT.obj V ⟶ rt.obj Y) (rT' : QT.obj W ⟶ rt.obj Y') (c : Y ⟶ Y')
    (hc : f₀.map q ≫ e₀ = t ≫ c₀)
    (he : f.map rX ≫ e ≫ b = aN ≫ QT.map e₀ ≫ rT')
    (ha : f.map (Q.map q) ≫ aN = aP ≫ QT.map (f₀.map q))
    (hr : QT.map c₀ ≫ rT' = rT ≫ rt.map c) :
    f.map (Q.map q ≫ rX) ≫ e ≫ b = aP ≫ (QT.map t ≫ rT) ≫ rt.map c := by
  rw [f.map_comp_assoc, he, ← Category.assoc, ha]
  simp only [Category.assoc, ← QT.map_comp_assoc]
  rw [hc]
  simp only [QT.map_comp, Category.assoc]
  rw [hr]

private theorem reverse_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (ProEtale.scalarPullbackReverseEtale φ f).app (_root_.DerivedCategory.Q.obj P) ≫
      L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ X P) ≫
      scalarGeometricRepresentative B f
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) =
    (scalarExtension φ T).map (scalarGeometricRepresentative A f P) ≫
      scalarExtensionRepresentative φ T
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).inv.app P) := by
  let adx : scalarExtension φ X ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ :=
    Adjunction.ofIsRightAdjoint _
  let adt' : scalarExtension φ T ⊣ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ :=
    Adjunction.ofIsRightAdjoint _
  let ec := Functor.mapHomologicalComplexCompIso (upperStarRestrictScalarsIsoSheaf φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (upperStar (ModuleCat.{u + 1} B) f ⋙
        Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).symm
  have hk := scalar_complex_unit φ f P
  have hef (N : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :=
    scalarRestrictionPullbackIso_representative φ f N
  unfold ProEtale.scalarPullbackReverseEtale
  apply normalized_scalar_mate adx adt'
    L(upperStar (ModuleCat.{u + 1} A) f) L(upperStar (ModuleCat.{u + 1} B) f)
    (scalarRestrictionPullbackIso φ f).hom
    (_root_.DerivedCategory.Q.obj P)
    (_root_.DerivedCategory.Q.obj
      (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P))
    (_root_.DerivedCategory.Q.obj
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P))
    _ _ (scalarExtensionRepresentative φ X P)
    (scalarExtensionRepresentative φ T
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P))
    (scalarGeometricRepresentative A f P) _ _
    (_root_.DerivedCategory.Q.map (scalarCochainUnit φ X P) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P))
    (_root_.DerivedCategory.Q.map (scalarCochainUnit φ T
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj
          (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P)))
    (scalar_rep_unit φ X P)
    (scalar_rep_unit φ T
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P))
  apply representative_square_unit
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    ((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ))
    L(upperStar (ModuleCat.{u + 1} A) f)
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
    (scalarCochainUnit φ X P)
    (scalarCochainUnit φ T
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P))
    (ec.hom.app _) ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex
      (.up ℤ) |>.map ((scalarSheafPullbackComplexIso φ f).inv.app P))
    _ _ _ _ _
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
      (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P)))
    _ (_root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).inv.app P))
    hk (hef _) (scalarGeometricRepresentative_naturality A f _)
  exact (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.naturality
    ((scalarSheafPullbackComplexIso φ f).inv.app P)

private theorem inverse_normalization_app
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (τ : F ⟶ G) [IsIso τ] (X : C) {W Z : D}
    (a : G.obj X ⟶ W) (b : F.obj X ⟶ Z) (c : Z ≅ W)
    (h : τ.app X ≫ a = b ≫ c.hom) :
    (asIso τ).inv.app X ≫ b = a ≫ c.inv := by
  exact inverse_normalization ((asIso τ).app X) a b c h

private theorem unique_choice_eq {α : Sort*} {p : α → Prop}
    (h : ∃! x, p x) (a : α) (ha : p a) : a = h.choose := by
  exact h.choose_spec.2 a ha

private theorem scalarPullback_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ProEtale.scalarPullbackEtaleIsoFromMate φ f = scalarPullbackIso φ f := by
  apply unique_choice_eq (scalarPullbackIso_existsUnique φ f)
  intro P _hP
  have := (ProEtale.scalarPullbackReverse_isIso φ f).2
  have h := inverse_normalization_app (ProEtale.scalarPullbackReverseEtale φ f)
    (_root_.DerivedCategory.Q.obj P)
    (L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ X P) ≫
      scalarGeometricRepresentative B f
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P))
    ((scalarExtension φ T).map (scalarGeometricRepresentative A f P) ≫
      scalarExtensionRepresentative φ T
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P))
    (_root_.DerivedCategory.Q.mapIso ((scalarSheafPullbackComplexIso φ f).app P).symm)
    (by simpa only [Iso.app_hom, Iso.app_inv, asIso_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc] using reverse_normalization φ f P)
  simpa only [ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc] using h

end AlgebraicGeometry.Etale

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint
end CanonicalScalarPullbackIdentification

namespace AlgebraicGeometry.ProEtale
/-- The reused normalized comparison is the original inverse scalar mate.
Source: Stacks 07A4, 0G7E and 07A7
(blueprint: lem-sfb-etale-proetale-scalar-mate).
Proof: the ordinary reverse mate equals the inverse ordinary scalar/pullback
comparison by iterated mates and the restriction/direct-image adjunction identity.
Its scalar-unit equation holds degreewise on cochains. The exact derived geometric
representatives commute with the localized restriction square. Taking the derived
scalar adjunction transpose proves the reverse normalization. Invert that equation
and use uniqueness of the normalized forward comparison on K-flat representatives.
All helpers above prove these equations, with no additional hypotheses or holes. -/
private theorem scalarPullbackEtaleIso_eq_fromMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarPullbackEtaleIso a f = scalarPullbackEtaleIsoFromMate a f := by
  exact (Etale.scalarPullback_eq a f).symm
end AlgebraicGeometry.ProEtale
