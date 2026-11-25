/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCompactificationGraphMap
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-!
# Constructed graph comparisons for compact supports

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Inclusion of compactly supported sheaf sections into direct image.
Source: SGA 4 XVII 6.2.11
(auxiliary; not a blueprint node). -/
noncomputable def compactificationSheafToDirectImage
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} {f : U ⟶ X}
    (c : Compactification f) :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g ⟶ lowerStar (ModuleCat.{u + 1} A) f :=
  Functor.whiskerRight (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g) ≫
    (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom

/-- The specified sum-extension exchange, descended termwise and inverted.
Source: Stacks Project Tag 03S6
(auxiliary; not a blueprint node). -/
noncomputable def exactEtaleSumExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f)
          inferInstance).mapDerivedCategory :=
  haveI := isIso_etaleLowerShriekBaseChangeMap A g f
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (etaleLowerShriekBaseChangeMap A g f)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The proper exchange followed by inverse open-extension exchange, using exact derived
inverse image. The transport from `L(g^*)` is the canonical exact-functor comparison.
Source: SGA 4 XVII 5.2.2
(auxiliary; not a blueprint node). -/
noncomputable def exactCompactSupportExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) :=
  Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
    rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g f).flip c ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd g f)).hom _

section HomotopyNormalization
attribute [local instance 2000] Abelian.toPreadditive

/-- The natural transformation underlying the homotopy comparison, assembled from
exact-functor factors and the right-derived unit. No new objects are chosen.
Source: Stacks Project Tag 015F (auxiliary; not a blueprint node). -/
noncomputable def normalizationHomotopyTransformation
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (R : D ⥤ E)
    [S.Additive] [O.Additive] [R.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (a : S ⟶ O ⋙ R) :
    DerivedCategory.Qh ⋙ S.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ (O.mapDerivedCategory ⋙ R.rightDerivedFunctor) :=
  S.mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight (a.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (O.mapHomotopyCategory (.up ℤ)) R.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight O.mapDerivedCategoryFactorsh.inv R.rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

/-- The homotopy formula for an exact source and open factor followed by a right derived
functor. This is the explicit five-factor composite, with no choices of new objects.
Source: Stacks Project Tag 015F (auxiliary; not a blueprint node). -/
noncomputable def normalizationHomotopyComponent
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (R : D ⥤ E)
    [S.Additive] [O.Additive] [R.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (a : S ⟶ O ⋙ R) (K : HomotopyCategory C (.up ℤ)) :
    S.mapDerivedCategory.obj (DerivedCategory.Qh.obj K) ⟶
      R.rightDerivedFunctor.obj (O.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) :=
  S.mapDerivedCategoryFactorsh.hom.app K ≫
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app K) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)).inv.app K) ≫
    R.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K) ≫
    R.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app K)

/-- The generic natural transformation has the specified five-factor component.
Source: Stacks Project Tag 015F (auxiliary; not a blueprint node). -/
theorem normalizationHomotopyTransformation_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (R : D ⥤ E)
    [S.Additive] [O.Additive] [R.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (a : S ⟶ O ⋙ R) (K : HomotopyCategory C (.up ℤ)) :
    (normalizationHomotopyTransformation S O R a).app K =
      normalizationHomotopyComponent S O R a K := by
  simp only [normalizationHomotopyTransformation, normalizationHomotopyComponent,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

/-- A termwise sheaf comparison followed by the total-right-derived comparison.
This is a map on homotopy representatives, with no boundedness condition.
Source: SGA 4 XVII 6.2.11
(auxiliary; not a blueprint node). -/
noncomputable def compactSupportComparisonOnHomotopy
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (DerivedCategory.Qh.obj K) :=
  normalizationHomotopyComponent
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (lowerStar (ModuleCat.{u + 1} A) c.g) a K

/-- Descend a natural transformation through a localization without choosing any data.
Source: Stacks Project Tag 04VG
(auxiliary; not a blueprint node). -/
@[irreducible]
noncomputable def normalizationLocalizationDesc
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) : F ⟶ G :=
  (Localization.fullyFaithfulWhiskeringLeft L W E).preimage τ

/-- The localization descent recovers the original transformation on every representative.
Source: Stacks Project Tag 04VG
(auxiliary; not a blueprint node). -/
theorem normalizationLocalizationDesc_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) (K : C) :
    (normalizationLocalizationDesc L W τ).app (L.obj K) = τ.app K :=
by
  unfold normalizationLocalizationDesc
  exact congr_app ((Localization.fullyFaithfulWhiskeringLeft L W E).map_preimage τ) K

/-- The normalized comparison on all derived objects, obtained by full faithfulness of
precomposition with the homotopy localization. No isomorphism claim enters this construction.
Source: Stacks Project Tags 04VG and 015F
(auxiliary; not a blueprint node). -/
@[irreducible]
noncomputable def compactSupportDerivedComparison
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  normalizationLocalizationDesc DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (ComplexShape.up ℤ))
    (F := (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory)
    (G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (normalizationHomotopyTransformation
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g) a)

/-- The derived comparison has the prescribed value on every homotopy representative.
Source: Stacks Project Tag 04VG
(auxiliary; not a blueprint node). -/
theorem compactSupportDerivedComparison_app
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)) :
    (compactSupportDerivedComparison A f c a).app (DerivedCategory.Qh.obj K) =
      compactSupportComparisonOnHomotopy A f c a K := by
  rw [compactSupportDerivedComparison, normalizationLocalizationDesc_app]
  exact normalizationHomotopyTransformation_app _ _ _ _ _

end HomotopyNormalization

section IdentityNormalization
attribute [local instance 2000] Abelian.toPreadditive

end IdentityNormalization

end AlgebraicGeometry.Etale
