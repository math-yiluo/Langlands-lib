/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Canonical clopen alpha and its proper mate on the pro-etale site

Source: Stacks Project, Tags 09AF, 0F7B and 0B65
(blueprint: def-cbc-proetale-clopen-mate-data).

These constructions are independent of their transport property. They are moved
verbatim from FiniteClopenMateSiteTransport so that the alpha comparison can be
stated without depending on the theorem about its proper mate.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Equality transport for the canonical open extension functors.
Source: Stacks 09AF (blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcOpenCongr (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  h ▸ Iso.refl _

/-- Equality transport for inverse image, with its fixed canonical construction.
Source: Stacks 099R (blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcPullCongr (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} (h : j = k) :
    upperStar (ModuleCat.{u + 1} Λ) j ≅ upperStar (ModuleCat.{u + 1} Λ) k :=
  h ▸ Iso.refl _

/-- The identity/zero projection onto a clopen subscheme, on module sheaves.
It is the direct-image unit followed by the inverse of the canonical map
from extension by zero to direct image. Source: Stacks Tags 09AE and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenProjection (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶
      upperStar (ModuleCat.{u + 1} Λ) s ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit ≫
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) s)
      (inv (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s))

/-- The canonical sheaf alpha: inverse open-unit base change, projection onto the
clopen lift, and the canonical open and inverse-image compositors.
Source: Stacks Tags 09AF and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenAlphaSheaf (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback p i).flip
  inv (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback p i).flip.toCommSq) ≫
  Functor.whiskerRight
    (Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i))
      (cbcClopenProjection Λ (ProEtale.StrictTower.squareLift k r p i h)))
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)) ≫
  Functor.whiskerRight (Functor.associator _ _ _).inv
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)) ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft
    (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i) ⋙
      upperStar (ModuleCat.{u + 1} Λ) (ProEtale.StrictTower.squareLift k r p i h))
    ((proEtaleOpenExtensionComp Λ
        (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)).inv ≫
      (cbcOpenCongr Λ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((upperStarComp (ModuleCat.{u + 1} Λ)
      (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (cbcPullCongr Λ (pullback.lift_snd k r h)).hom)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)

/-- The same prescribed alpha on bounded-below derived categories. Exactness of all
four sheaf functors identifies the right-derived base-change map with termwise alpha.
Source: Stacks Tags 015F, 09AF and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenAlphaPlus (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus :=
  Functor.whiskerRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)).inv _ ≫
  Functor.rightDerivedFunctorPlusBaseChange (cbcClopenAlphaSheaf Λ k i r p h) ≫
  Functor.whiskerLeft _
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)).hom

/-- The proper-adjunction mate of the specified clopen alpha on this site.
Source: Stacks Tags 0B65 and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (mateEquiv (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) r)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) p)
    (TwoSquare.mk _ _ _ _ (cbcClopenAlphaPlus Λ k i r p h)))

end AlgebraicGeometry.ProEtale
