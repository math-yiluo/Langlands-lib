/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# Finite-level exceptional inverse image in canonical coefficient coordinates

The functor below is literally Rν_* followed by the etale right adjoint and then ν^*.
It is defined on the ordinary derived category; its meaningful domain is D⁺.
No ambient pro-etale adjunction is used or assumed.

## Main definitions

- `sfFiniteExceptionalFixed` and `sfFiniteExceptional`: the finite-level functor in
  fixed-scalar and intrinsic coordinates.
- `sfFiniteExceptionalOpenComparison`: the canonical comparison-site paste of the
  etale exceptional mate, using the specified site-square and restriction comparisons.

## References

* Stacks Tag 099R and localization
* Stacks Tags 099R and 07A5
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The ordinary derived support candidate attached to a specified compactification. -/
noncomputable abbrev sfFixedCompactSupport (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory ⋙
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor

/-- Finite-level exceptional inverse image: the existing etale adjoint, transported
through the exact comparison pullback and the ordinary right derived comparison image.
The compactification instance is the one specified by c. Thus no choice of an arbitrary
pro-etale right adjoint enters the definition. -/
noncomputable def sfFiniteExceptionalFixed (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  letI := c.hasCompactification
  (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).rightDerivedFunctor ⋙
    Etale.rightDerivedUpperShriek (ULift.{u + 1, u} A) f ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory

/-- The same finite-level functor in the recorded intrinsic constant-ring category.
The realization equivalences are the specified ones, rather than arbitrary equivalences. -/
noncomputable def sfFiniteExceptional (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A :=
  (sfIntrinsicDerivedEquivalence Y A).inverse ⋙ sfFiniteExceptionalFixed A c ⋙
    (sfIntrinsicDerivedEquivalence X A).functor

/-- Comparison and an open localization commute as restriction functors. -/
noncomputable def sfComparisonOpenRestrictionIso (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
        Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ≅
      upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U :=
  Functor.isoWhiskerLeft
      (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X)
      (Etale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j) ≪≫
    (Iso.refl _) ≪≫
    Functor.isoWhiskerRight
      (upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).symm
      (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U)

/-- The derived comparison direct image commutes with restriction to an open.
This is derived from the actual identity of localization restrictions. All first
functors preserve K-injectives: comparison direct image is right adjoint to exact ν^*,
and open restriction is right adjoint to exact extension by zero. -/
noncomputable def sfDerivedComparisonOpenRestrictionIso (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).rightDerivedFunctor ⋙
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ≅
      sfFixedDerivedPullback A j ⋙
        (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).rightDerivedFunctor :=
  letI := (comparisonAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).preservesKInjectiveComplexes
  letI := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).preservesKInjectiveComplexes
  Functor.isoWhiskerLeft
      (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).rightDerivedFunctor
      (Etale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (sfComparisonOpenRestrictionIso A j) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).rightDerivedFunctorIsoMapDerivedCategory _

/-- Naturality of the identity components of the comparison-site pullback square. -/
theorem sfToProEtBaseChange_naturality {U X : Scheme.{u}} (j : U ⟶ X)
    {V W : X.Etale} (h : V ⟶ W) :
    (toProEt X ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).map h ≫ 𝟙 _ =
      𝟙 _ ≫ (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j ⋙ toProEt U).map h := by
  ext
  simp
  rfl

/-- The canonical site square identifying inclusion followed by base change with base
change followed by inclusion. -/
noncomputable def sfToProEtBaseChangeIso {U X : Scheme.{u}} (j : U ⟶ X) :
    toProEt X ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ j ≅
      MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j ⋙ toProEt U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (sfToProEtBaseChange_naturality j)

/-- The site-square identification on direct image. -/
noncomputable def sfComparisonDirectImageCompIso (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ≅
      comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U ⋙
        Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j :=
  letI := isContinuous_toProEt U
  letI := ProEt.isContinuous_overPullback j
  letI : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j).IsContinuous
      X.smallEtaleTopology U.smallEtaleTopology := Etale.isContinuous_overPullback j
  letI := Functor.isContinuous_comp (toProEt X)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j)
      X.smallEtaleTopology (ProEt.topology X) (ProEt.topology U)
  letI := Functor.isContinuous_comp (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j)
    (toProEt U) X.smallEtaleTopology U.smallEtaleTopology (ProEt.topology U)
  Functor.sheafPushforwardContinuousComp (toProEt X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X.smallEtaleTopology
      (ProEt.topology X) (ProEt.topology U) ≪≫
    Functor.sheafPushforwardContinuousIso (sfToProEtBaseChangeIso j)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X.smallEtaleTopology (ProEt.topology U) ≪≫
    (Functor.sheafPushforwardContinuousComp
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j) (toProEt U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X.smallEtaleTopology
      U.smallEtaleTopology (ProEt.topology U)).symm

/-- The canonical inverse-image comparison is the conjugate of the actual site square. -/
noncomputable def sfComparisonPullbackIso (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U :=
  (conjugateIsoEquiv
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).comp
      (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U))
    ((comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))).symm
    (sfComparisonDirectImageCompIso A j).symm

/-- The exact comparison square on ordinary derived categories. -/
noncomputable def sfDerivedComparisonPullbackIso (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory ⋙
        sfFixedDerivedPullback A j ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (sfComparisonPullbackIso A j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.ProEtale
