/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenIdentificationNormalization
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Coefficient naturality of the proper/open refinement

The auxiliary maps implement the coefficient normalizations. Scalar extension
and the K-flat-normalized scalar/pullback comparison are existing constructions.

## References

* Stacks 0G7E and 0GL6
* Stacks 03DJ, 06YS and 0GL6
* Stacks 0F7I and 0GL6, with the explicit clopen-section argument
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The canonical tensor/pullback comparison, expressed using exact inverse image.
It transports the existing K-flat-normalized comparison along the canonical
identification of derived inverse image with termwise inverse image. -/
def properOpenCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (v : W ⟶ T) :
    scalarExtension φ T ⋙ (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ scalarExtension φ W :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).symm ≪≫
    scalarPullbackIso φ v ≪≫
      Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v) _

/-- The inverse open coefficient map, defined by its prescribed open-unit transpose. -/
def properOpenCoefficientOpenInverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A W) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
        ((scalarExtension φ W).obj M) ⟶
      (scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).homEquiv _ _).symm
      ((scalarExtension φ W).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app M) ≫
        (properOpenCoefficientPullbackIso φ j).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M))

/-- The specified inverse open coefficient map is invertible for arbitrary derived inputs. -/
theorem properOpenCoefficientOpenInverse_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A W) :
    IsIso (properOpenCoefficientOpenInverse φ j M) := by
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  have hu : IsIso adj.unit :=
    isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit _ _
  have : (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.Full :=
    adj.fullyFaithfulLOfIsIsoUnit.full
  have : (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.Faithful :=
    adj.fullyFaithfulLOfIsIsoUnit.faithful
  -- Composite left adjoints give an isomorphism of objects; no normalization is needed.
  let e := (conjugateIsoEquiv
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).comp
      (adj.ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm))).symm
    (scalarRestrictionPullbackIso φ j) |>.symm
  have : IsIso (adj.counit.app
      ((scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M))) :=
    adj.isIso_counit_app_of_iso (e.app M)
  -- The target lies in the essential image of the fully faithful open extension.
  unfold properOpenCoefficientOpenInverse
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The open tensor isomorphism with the inverse fixed by the open-unit transpose. -/
def properOpenCoefficientOpenIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A W) :
    (scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
        ((scalarExtension φ W).obj M) :=
  (@asIso _ _ _ _ (properOpenCoefficientOpenInverse φ j M)
    (properOpenCoefficientOpenInverse_isIso φ j M)).symm

/-- The existing theta-normalized proper/open map, viewed in the unbounded category.
Only the canonical compatibility of bounded and unbounded direct image is inserted. -/
def properOpenComparisonAmbient
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T₁ T₂ X : Scheme.{u}} (v : T₁ ⟶ T₂) [IsProper v]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ v = j₂)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j₂).mapDerivedCategory.obj K.obj ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) v).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj K.obj) :=
  (properOpenComparison A v j₁ j₂ h K).hom ≫
    (lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctorPlusCompatibility.hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategoryPlus.obj K)

-- Coherence to be checked on the flat K-flat representatives normalizing lambda.
private theorem coefficientPullback_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    (v : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app ((scalarExtension φ T₂).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j₁).mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ v).hom.app N) ≫
      (properOpenCoefficientPullbackIso φ j₁).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
      (properOpenCoefficientPullbackIso φ j₂).hom.app N ≫
        (scalarExtension φ X).map
          ((Functor.mapDerivedCategoryNatIso
              (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app N) := by
  simpa only [properOpenCoefficientPullbackIso] using
    scalarPullback_composition φ v j₁ j₂ h N

private theorem coefficientMate_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (v : W ⟶ T)
    (M : DerivedCategoryModule A W) :
    (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory.map ((scalarMate φ v).app M) ≫
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v)).counit.app
          ((scalarExtension φ W).obj M)) =
      (properOpenCoefficientPullbackIso φ v).hom.app
          (((lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor).obj M) ≫
        (scalarExtension φ W).map
          (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).ofNatIsoLeft
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v)).counit.app M) := by
  have hm := mateEquiv_counit
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v)
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ v).hom) M
  apply (cancel_epi
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).hom.app
      ((scalarExtension φ T).obj
        (((lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor).obj M)))).mp
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.comp_obj]
  rw [← reassoc_of%
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).hom.naturality
      ((scalarMate φ v).app M)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [show (upperStar (ModuleCat.{u + 1} B) v).leftDerivedFunctor.map
      ((scalarMate φ v).app M) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).counit.app
        ((scalarExtension φ W).obj M) = _ from hm]
  simp only [properOpenCoefficientPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  simp [← Functor.map_comp, TwoSquare.mk]

private theorem coefficientOpen_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A W) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app
        ((scalarExtension φ W).obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (properOpenCoefficientOpenIso φ j M).inv =
      (scalarExtension φ W).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app M) ≫
        (properOpenCoefficientPullbackIso φ j).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) := by
  change ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).homEquiv _ _)
      (properOpenCoefficientOpenInverse φ j M) = _
  exact Equiv.apply_symm_apply _ _

-- Restriction to the common open, expressed using the geometric counit.
private def refinementRestriction
    (A : Type (u + 1)) [CommRing A]
    {T₁ T₂ X : Scheme.{u}} (v : T₁ ⟶ T₂)
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂) :
    (lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategory :=
  let k := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  { app M := k.hom.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.map
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v)).counit.app M)
    naturality {M N} f := by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [reassoc_of% k.hom.naturality
        (((lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctor).map f)]
      rw [← Functor.map_comp, Adjunction.counit_naturality, Functor.map_comp]
      exact (Category.assoc _ _ _).symm }

set_option backward.isDefEq.respectTransparency false in
private theorem refinementRestriction_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T₁ T₂ X : Scheme.{u}} (v : T₁ ⟶ T₂) [IsProper v]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ v = j₂)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j₂).homEquiv _ _
        (properOpenComparisonAmbient A v j₁ j₂ h K) ≫
      (refinementRestriction A v j₁ j₂ h).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj K.obj) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j₁).unit.app K.obj ∧
      IsIso ((refinementRestriction A v j₁ j₂ h).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj K.obj)) := by
  let M := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategoryPlus.obj K
  let e := (lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctorPlusCompatibility.hom.app M
  have hn := properOpenIdentification_unit A v j₁ j₂ h K
  have hn' := congrArg _root_.DerivedCategory.Plus.ι.map hn
  have hc : (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map e ≫
      (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v)).counit.app M.obj) =
      _root_.DerivedCategory.Plus.ι.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).derivedPlus.counit.app M) := by
    rw [← Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
    simp only [Adjunction.derivedAdjunctionPlus,
      Adjunction.map_restrictFullyFaithful_counit_app]
    simp [Functor.mapDerivedCategoryPlusCompatibility, e,
      leftDerivedUpperStarIsoMapDerivedCategory, derivedUpperStarLowerStarAdjunction]
  have hu {T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j] :
      _root_.DerivedCategory.Plus.ι.map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
            (ModuleCat.{u + 1} A) j).unit.app K) =
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).unit.app K.obj := by
    unfold derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      Adjunction.mapDerivedCategoryPlusAdjunction
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
      Iso.refl_hom, NatTrans.id_app]
    change (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit.app K.obj ≫
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          (𝟙 ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
            K.obj)) ≫ 𝟙 _ = _
    simp only [Category.comp_id]
    exact (congrArg (fun z ↦
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app K.obj ≫ z)
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map_id _)).trans
        (Category.comp_id _)
  let k := Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have hk : _root_.DerivedCategory.Plus.ι.map
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} A) j₁ v j₂ h.symm).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) v).obj M)) =
      k.hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) v).obj M).obj := by
    simp only [upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, k]
    rfl
  simp only [Functor.map_comp] at hn'
  rw [hu, hk] at hn'
  have ht : (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory.map e ≫
      (refinementRestriction A v j₁ j₂ h).app M.obj =
      _root_.DerivedCategory.Plus.ι.map (properOpenIdentification A v j₁ j₂ h K).hom ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j₁).unit.app K.obj := by
    dsimp only [refinementRestriction, M]
    erw [reassoc_of% k.hom.naturality e]
    rw [← Functor.map_comp, hc]
    exact hn'.symm
  have : IsIso e := by dsimp [e]; infer_instance
  have hi : IsIso ((refinementRestriction A v j₁ j₂ h).app M.obj) := by
    have : IsIso ((upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory.map e ≫
        (refinementRestriction A v j₁ j₂ h).app M.obj) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory.map e) _
  refine ⟨?_, hi⟩
  have ha : (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} A) j₂).homEquiv _ _
      (properOpenComparison A v j₁ j₂ h K) =
      (properOpenIdentification A v j₁ j₂ h K).inv := by
    change ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} A) j₂).homEquiv _ _)
        (((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} A) j₂).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have ha' := congrArg _root_.DerivedCategory.Plus.ι.map ha
  simp only [Adjunction.homEquiv_unit, Functor.map_comp] at ha'
  rw [hu] at ha'
  simp only [properOpenComparisonAmbient, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc]
  erw [ht]
  simp only [← Category.assoc]
  have ha'' : (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j₂).unit.app K.obj ≫
      (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory.map
        (properOpenComparison A v j₁ j₂ h K).hom =
      _root_.DerivedCategory.Plus.ι.map (properOpenIdentification A v j₁ j₂ h K).inv := ha'
  rw [ha'']
  have hid := congrArg _root_.DerivedCategory.Plus.ι.map
    (properOpenIdentification A v j₁ j₂ h K).inv_hom_id
  simp only [Functor.map_comp] at hid
  exact (congrArg (fun z ↦ z ≫
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j₁).unit.app K.obj) hid).trans (Category.id_comp _)

-- The counit mate equation turns pullback-composition coherence into restriction coherence.
private theorem restriction_coefficient_mate
    {CA DA EA CB DB EB : Type*}
    [Category* CA] [Category* DA] [Category* EA]
    [Category* CB] [Category* DB] [Category* EB]
    {FA : EA ⥤ DA} {RA : DA ⥤ EA} {FB : EB ⥤ DB} {RB : DB ⥤ EB}
    (adjA : FA ⊣ RA) (adjB : FB ⊣ RB)
    (U₁A : DA ⥤ CA) (U₂A : EA ⥤ CA) (U₁B : DB ⥤ CB) (U₂B : EB ⥤ CB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (kA : U₂A ≅ FA ⋙ U₁A) (kB : U₂B ≅ FB ⋙ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (lv : Q₂ ⋙ FB ≅ FA ⋙ Q₁) (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hc : ∀ M, FB.map (χ.app M) ≫ adjB.counit.app (Q₁.obj M) =
      lv.hom.app (RA.obj M) ≫ Q₁.map (adjA.counit.app M))
    (hk : ∀ N, kB.hom.app (Q₂.obj N) ≫ U₁B.map (lv.hom.app N) ≫
        l₁.hom.app (FA.obj N) = l₂.hom.app N ≫ QX.map (kA.hom.app N))
    (M : DA) :
    U₂B.map (χ.app M) ≫ kB.hom.app (RB.obj (Q₁.obj M)) ≫
        U₁B.map (adjB.counit.app (Q₁.obj M)) ≫ l₁.hom.app M =
      l₂.hom.app (RA.obj M) ≫ QX.map (kA.hom.app (RA.obj M)) ≫
        QX.map (U₁A.map (adjA.counit.app M)) := by
  rw [reassoc_of% kB.hom.naturality (χ.app M)]
  rw [← U₁B.map_comp_assoc, hc, U₁B.map_comp]
  simp only [Category.assoc]
  have hn := l₁.hom.naturality (adjA.counit.app M)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [hn]
  simpa only [Category.assoc, Functor.comp_obj] using
    congrArg (fun z ↦ z ≫ QX.map (U₁A.map (adjA.counit.app M))) (hk (RA.obj M))

-- Naturality of restriction and the two open-unit transposes imply the coefficient square.
private theorem coefficient_refinement_of_restriction
    {CA DA EA CB DB EB : Type*}
    [Category* CA] [Category* DA] [Category* EA]
    [Category* CB] [Category* DB] [Category* EB]
    {J₁A : CA ⥤ DA} {J₂A : CA ⥤ EA}
    {U₁A : DA ⥤ CA} {U₂A : EA ⥤ CA}
    {J₁B : CB ⥤ DB} {J₂B : CB ⥤ EB}
    {U₁B : DB ⥤ CB} {U₂B : EB ⥤ CB}
    (a₁A : J₁A ⊣ U₁A) (a₂A : J₂A ⊣ U₂A)
    (a₁B : J₁B ⊣ U₁B) (a₂B : J₂B ⊣ U₂B)
    (RA : DA ⥤ EA) (RB : DB ⥤ EB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (tA : RA ⋙ U₂A ⟶ U₁A) (tB : RB ⋙ U₂B ⟶ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hχ : ∀ M, U₂B.map (χ.app M) ≫ tB.app (Q₁.obj M) ≫ l₁.hom.app M =
      l₂.hom.app (RA.obj M) ≫ QX.map (tA.app M))
    (K : CA) (αA : J₂A.obj K ⟶ RA.obj (J₁A.obj K))
    (αB : J₂B.obj (QX.obj K) ⟶ RB.obj (J₁B.obj (QX.obj K)))
    (b₁ : Q₁.obj (J₁A.obj K) ≅ J₁B.obj (QX.obj K))
    (b₂ : Q₂.obj (J₂A.obj K) ≅ J₂B.obj (QX.obj K))
    (hb₁ : a₁B.unit.app (QX.obj K) ≫ U₁B.map b₁.inv =
      QX.map (a₁A.unit.app K) ≫ l₁.inv.app (J₁A.obj K))
    (hb₂ : a₂B.unit.app (QX.obj K) ≫ U₂B.map b₂.inv =
      QX.map (a₂A.unit.app K) ≫ l₂.inv.app (J₂A.obj K))
    (hA : a₂A.homEquiv _ _ αA ≫ tA.app (J₁A.obj K) = a₁A.unit.app K)
    (hB : a₂B.homEquiv _ _ αB ≫ tB.app (J₁B.obj (QX.obj K)) =
      a₁B.unit.app (QX.obj K))
    [Mono (tB.app (J₁B.obj (QX.obj K)))] :
    Q₂.map αA ≫ χ.app (J₁A.obj K) ≫ RB.map b₁.hom = b₂.hom ≫ αB := by
  apply (cancel_epi b₂.inv).mp
  apply (a₂B.homEquiv _ _).injective
  apply (cancel_mono (tB.app (J₁B.obj (QX.obj K)))).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hB]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hb₂]
  simp only [Category.assoc]
  have hn := tB.naturality b₁.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  have hc := hχ (J₁A.obj K)
  have hc' : U₂B.map (χ.app (J₁A.obj K)) ≫ tB.app (Q₁.obj (J₁A.obj K)) =
      l₂.hom.app (RA.obj (J₁A.obj K)) ≫ QX.map (tA.app (J₁A.obj K)) ≫
        l₁.inv.app (J₁A.obj K) := by
    simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id] using
      congrArg (fun z ↦ z ≫ l₁.inv.app (J₁A.obj K)) hc
  rw [reassoc_of% hc']
  rw [reassoc_of% l₂.hom.naturality αA]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← QX.map_comp_assoc, ← QX.map_comp_assoc]
  change QX.map (a₂A.homEquiv _ _ αA ≫ tA.app (J₁A.obj K)) ≫ _ = _
  rw [hA]
  rw [← reassoc_of% hb₁]
  rw [← U₁B.map_comp, Iso.inv_hom_id, U₁B.map_id, Category.comp_id]

/-- Coefficient extension respects the specified proper/open refinement arrow. -/
theorem properOpenComparison_coefficient_refinement
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian T₁] [IsNoetherian T₂]
    (v : T₁ ⟶ T₂) [IsProper v]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ v = j₂)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj K.obj)) :
    (scalarExtension φ T₂).map (properOpenComparisonAmbient A v j₁ j₂ h K) ≫
        (scalarMate φ v).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj K.obj) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} B) v).map
          (properOpenCoefficientOpenIso φ j₁ K.obj).hom =
      (properOpenCoefficientOpenIso φ j₂ K.obj).hom ≫
        properOpenComparisonAmbient B v j₁ j₂ h ⟨(scalarExtension φ X).obj K.obj, hQ⟩ := by
  let kA := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  let kB := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have hχ : ∀ M : DerivedCategoryModule A T₁,
      (upperStar (ModuleCat.{u + 1} B) j₂).mapDerivedCategory.map
          ((scalarMate φ v).app M) ≫
        (refinementRestriction B v j₁ j₂ h).app ((scalarExtension φ T₁).obj M) ≫
        (properOpenCoefficientPullbackIso φ j₁).hom.app M =
      (properOpenCoefficientPullbackIso φ j₂).hom.app
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) v).obj M) ≫
        (scalarExtension φ X).map ((refinementRestriction A v j₁ j₂ h).app M) := by
    intro M
    simpa only [refinementRestriction, kA, kB, rightDerivedLowerStar,
      Functor.map_comp, Category.assoc] using
      restriction_coefficient_mate
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v))
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v))
        (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) j₁).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) j₂).mapDerivedCategory
        (scalarExtension φ X) (scalarExtension φ T₁) (scalarExtension φ T₂)
        kA kB (properOpenCoefficientPullbackIso φ j₁)
        (properOpenCoefficientPullbackIso φ j₂) (properOpenCoefficientPullbackIso φ v)
        (scalarMate φ v) (coefficientMate_counit φ v)
        (coefficientPullback_comp φ v j₁ j₂ h) M
  have hA := refinementRestriction_normalization A v j₁ j₂ h K
  have hB := refinementRestriction_normalization B v j₁ j₂ h
    ⟨(scalarExtension φ X).obj K.obj, hQ⟩
  have := hB.2
  exact coefficient_refinement_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j₁)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j₂)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j₁)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j₂)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) v)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) v)
    (scalarExtension φ X) (scalarExtension φ T₁) (scalarExtension φ T₂)
    (refinementRestriction A v j₁ j₂ h) (refinementRestriction B v j₁ j₂ h)
    (properOpenCoefficientPullbackIso φ j₁) (properOpenCoefficientPullbackIso φ j₂)
    (scalarMate φ v) hχ K.obj
    (properOpenComparisonAmbient A v j₁ j₂ h K)
    (properOpenComparisonAmbient B v j₁ j₂ h ⟨(scalarExtension φ X).obj K.obj, hQ⟩)
    (properOpenCoefficientOpenIso φ j₁ K.obj) (properOpenCoefficientOpenIso φ j₂ K.obj)
    (coefficientOpen_unit φ j₁ K.obj) (coefficientOpen_unit φ j₂ K.obj) hA.1 hB.1

end AlgebraicGeometry.Etale
