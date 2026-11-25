/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.FlatModelGeneration
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Open coefficient tensor, evaluation, and finite Tor bounds

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-dualizing.proof.md, paragraphs 2-3; Stacks Tags 03DI, 03DJ,
03S6, 03TT, 0GKB, 06YY, 0E8I and 0GL1
(blueprint: lem-coef-dualizing-open-tensor).

The comparison is the existing B-linear `openScalarExtension`, with the existing
`openScalarRestrictionMap` mate in its evaluation equation. The ordinary
composite is applied to complexes before localization. No faithfulness of derived
stalk functors on morphisms is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The ordinary open tensor/evaluation composite, using the fixed ordinary scalar
comparisons and the actual open adjunction counit. Its degreewise application is
the direct-sum total tensor comparison with B in degree zero.
Source: Stacks 03DI, 0E8I (blueprint: lem-coef-dualizing-open-tensor). -/
def openTensorEvaluationZero
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} A) j ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
        ProEtale.etaleSheafExtendScalars φ Y ⟶ ProEtale.etaleSheafExtendScalars φ Y :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) j)
      (openScalarExtensionZero φ j).hom ≫
    Functor.whiskerRight (openScalarRestrictionZero φ j).hom
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j) ≫
    Functor.whiskerLeft (ProEtale.etaleSheafExtendScalars φ Y)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).counit

private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private theorem scalarOpenInverseMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))) =
      ((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv := by
  rw [uniq_eq_conjugate]
  exact
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))

private theorem derivedEvaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : DerivedCategoryModule A X) :
    (openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj T) ≫
        (derivedExtension (A := B) j).map ((openScalarRestrictionMap φ j).app T) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ X).obj T) =
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let u := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (openDerivedRestrictScalarsIso φ j).inv)
  have h := mateEquiv_counit_symm a b α T
  have hm : ((mateEquiv a b).symm α) = (openScalarExtension φ j).inv :=
    scalarOpenInverseMate a b x u (openDerivedRestrictScalarsIso φ j)
  change _ = ((mateEquiv a b).symm α).app _ ≫ _ at h
  rw [hm] at h
  change (derivedExtension (A := B) j).map ((openScalarRestrictionMap φ j).app T) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).counit.app
        ((scalarExtension φ X).obj T) =
    (openScalarExtension φ j).inv.app ((derivedRestriction (A := A) j).obj T) ≫
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T) at h
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    congrArg (fun t ↦ (openScalarExtension φ j).hom.app
      ((derivedRestriction (A := A) j).obj T) ≫ t) h

private theorem ordinaryEvaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    openTensorEvaluationZero φ j = Functor.whiskerRight
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit
      (ProEtale.etaleSheafExtendScalars φ Y) := by
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := ProEtale.etaleSheafExtendScalarsAdjunction φ Y
  let u := ProEtale.etaleSheafExtendScalarsAdjunction φ U
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (openRestrictScalarsIso φ j).inv)
  have hr : α = (openScalarRestrictionZero φ j).hom := by
    dsimp only [α]
    rw [openRestrictScalarsIso_inv_eq, ordinary_reverse_eq]
    have hh := uniq_eq_conjugate
      (x.comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp u) (Iso.refl _)
    exact congrArg Iso.inv hh.symm
  have hm : ((mateEquiv a b).symm α) = (openScalarExtensionZero φ j).inv :=
    scalarOpenInverseMate a b x u (openRestrictScalarsIso φ j)
  apply NatTrans.ext
  funext T
  have h := mateEquiv_counit_symm a b α T
  change _ = ((mateEquiv a b).symm α).app _ ≫ _ at h
  rw [hm] at h
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).map
      (α.app T) ≫ _ = _ at h
  rw [hr] at h
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).map
      ((openScalarRestrictionZero φ j).hom.app T) ≫ b.counit.app
        ((ProEtale.etaleSheafExtendScalars φ Y).obj T) =
    (openScalarExtensionZero φ j).inv.app ((upperStar (ModuleCat.{u + 1} A) j).obj T) ≫
      (ProEtale.etaleSheafExtendScalars φ Y).map (a.counit.app T) at h
  simpa only [openTensorEvaluationZero, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc] using
    congrArg (fun t ↦ (openScalarExtensionZero φ j).hom.app
      ((upperStar (ModuleCat.{u + 1} A) j).obj T) ≫ t) h

private theorem sourceBoundedConstructible
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {K : DerivedCategoryModule A X} (hK : DerivedCategory.isBoundedConstructible A X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  obtain ⟨c, d, -, hz⟩ := hK.2
  refine ⟨⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩, fun q ↦ ?_⟩
  · exact (_root_.DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hz q (.inl hq)
  · exact (_root_.DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hz q (.inr hq)
  · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hK.1 q)

private theorem finiteValueBoundedConstructible
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {K : DerivedCategoryModule A X}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K) :
    DerivedCategory.isBoundedConstructible A X K := by
  obtain ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, hcons⟩ := hK
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    (hcons q), min c d, d, min_le_right _ _, ?_⟩
  intro q hq
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ c).1 hc q
      (lt_of_lt_of_le hq (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ d).1 hd q hq

private theorem exactFlatFunctor_tor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {X Y : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hf : ∀ P, ObjectProperty.flat P → ObjectProperty.flat (F.obj P))
    {K : DerivedCategoryModule A X} {a b : ℤ}
    (ht : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    DerivedCategory.hasTorAmplitudeIn B Y a b (F.mapDerivedCategory.obj K) := by
  rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn] at ht ⊢
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn ht
  exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
    ((F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b fun q ↦ hf _ (hP q))

private theorem scalarBoundedConstructibleTor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K)
    (a b : ℤ) (hab : a ≤ b) (ht : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    DerivedCategory.isBoundedConstructible B X ((scalarExtension φ X).obj K) ∧
      DerivedCategory.hasTorAmplitudeIn B X a b ((scalarExtension φ X).obj K) := by
  let Kb : _root_.DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, (sourceBoundedConstructible hK).1⟩
  have hs := exists_etaleScalarFlatModel X A B φ a b hab Kb hK.1 ht
  have ht' := hs.2.2.2.2
  have hh := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
    (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht')
  refine ⟨⟨hs.2.2.2.1, a, b, hab, ?_⟩, ht'⟩
  intro q hq
  exact hq.elim
    (fun h ↦ (_root_.DerivedCategory.isGE_iff _ a).1 hh.1 q h)
    (fun h ↦ (_root_.DerivedCategory.isLE_iff _ b).1 hh.2 q h)

end AlgebraicGeometry.Etale
