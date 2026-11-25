/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.SmoothPurity.FixSiteOpenExchangeSheaf
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube

/-!
# Site comparison respects the normalized open base-change map

Source: Stacks Project, Tag 03S6 (`lemma-shriek-base-change`), with the normalized
comparison of Tag 09AF and pullback coherence of Tag 099R (blueprint:
`lem-fix-site-open-exchange`).  The theorem below states the ordinary derived
comparison equation for every bounded-below etale complex and arbitrary bottom
map `g`. The proof lifts the ordinary sheaf equation through exact-functor localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The derived site comparison for extension by zero, `c_j : N_X j_!^et ≅ j_!^proet N_U`,
the degreewise extension of the sheaf comparison of
proposition-comparison-immersions--1.  It is the same construction as the upstream
`mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso`, whose module cannot be
imported together with this item's side imports.
Source: Stacks Tag 09AF (`lemma-jshriek-comparison`), blueprint
`lem-fix-site-open-exchange`. -/
noncomputable def fixSiteOpenComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The inverse-image comparison, oriented as `rho_u : u_proet⁻¹ N_V ≅
N_T u_et⁻¹`: degreewise `comparisonUpperStarCompUpperStarIso`, the inverse of the canonical
comparison of proposition-comparison-etale-derived-category--5.  It is the same construction as the
upstream `mapDerivedCategoryComparisonUpperStarCompUpperStarIso`, whose module cannot be
imported together with this item's side imports.
Source: Stacks Tag 099R; blueprint `lem-fix-site-open-exchange`. -/
noncomputable def fixSitePullbackComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (u : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) u) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

section Localization

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory F]
  (R : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (S : E ⥤ F)
  [R.Additive] [G.Additive] [L.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def derivedFace (e : R ⋙ G ≅ L ⋙ S) :
    R.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ S.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso R G ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso L S).symm

private theorem derivedPlusFace (e : R ⋙ G ≅ L ⋙ S)
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
      (((Functor.mapDerivedCategoryPlusCompIso R G).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso e ≪≫
        Functor.mapDerivedCategoryPlusCompIso L S).hom.app K) =
      (derivedFace R G L S e).hom.app (DerivedCategory.Plus.ι.obj K) := by
  have hi : DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso R G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso R G).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso R G).inv.app
      (DerivedCategory.Plus.ι.obj K))).mp
    rw [← Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app R G K]
    rw [← Functor.map_comp]
    rw [Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    simp
    rfl
  simp only [derivedFace, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, hi, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]

end Localization

/-- The normalized site-comparison/open-exchange equation.
Source: Stacks Tag 03S6 (`lemma-shriek-base-change`), Tags 09AF and 099R
(blueprint: lem-fix-site-open-exchange).

For each bounded-below `K`, the left side is `g⁻¹(c_j)`, then the actual pro-etale
base-change isomorphism `e_j^proet`, then `j'_!(rho_h)`.  The right side is `rho_g`,
then `N_X'` of the actual etale base-change isomorphism `e_j^et`, then `c_{j'}`.  The
cartesian square is the chosen one of `sq`, read as an `IsPullback` witness.  The
inverse-unit normalization of `c_j` asserted by the node is the published statement
`openComparison_unit_normalization` (lem-sf-open-comparison-unit-normalization) about
the same sheaf comparison `openImmersionLowerShriekComparisonUpperStarIso`.

Proof:
1. The ordinary equation is `fixSiteOpenExchangeSheaf`: the inverse open exchanges
   satisfy their unit formulas; comparison-unit normalization and cartesian-square
   coherence identify the two inverse transposes under the open adjunction.
2. Apply `Functor.mapDerivedCategory_exactCube` to this equation and the six specified
   ordinary isomorphisms. Exactness permits degreewise passage to complexes and
   localization. The localization factors identify these maps with the stated derived
   comparisons, without any faithfulness assumption on localization.
3. Evaluate at the image of `K` under the bounded-below inclusion. The composition and
   natural-isomorphism compatibility formulas identify the etale bounded-below exchange
   with the corresponding unbounded derived face. For the inverse composition map,
   cancel its forward isomorphism and use functoriality.
4. All calculations include identity squares, empty opens, zero complexes and the zero
   coefficient ring. No additional hypothesis on `g` is used. -/
theorem fixSiteOpenExchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare gU j' j g)
    (K : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.map
        ((fixSiteOpenComparison Λ j).hom.app
          (DerivedCategory.Plus.ι.obj K)) ≫
      (ordinaryOpenExtensionBaseChangeIso Λ gU j' j g
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategory.map
        ((fixSitePullbackComparison Λ gU).hom.app
          (DerivedCategory.Plus.ι.obj K)) =
    (fixSitePullbackComparison Λ g).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.extensionZeroBaseChangeDerivedPlusIso Λ
            (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst
              sq.hom_snd)).hom.app K)) ≫
      (fixSiteOpenComparison Λ j').hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) gU).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) := by
  let A := ModuleCat.{u + 1} Λ
  let hp := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let q1 := openImmersionLowerShriekComparisonUpperStarIso A j
  let q2 := fixSiteOpenSheafExchangeIso Λ gU j' j g hp
  let q3 := comparisonUpperStarCompUpperStarIso A gU
  let q4 := comparisonUpperStarCompUpperStarIso A g
  let q5 := (@asIso _ _ _ _ _ (Etale.isIso_openImmersionLowerShriekBaseChangeMap
    A hp)).symm
  let q6 := openImmersionLowerShriekComparisonUpperStarIso A j'
  have hc := Functor.mapDerivedCategory_exactCube
    (Etale.openImmersionLowerShriek A j) (comparisonUpperStar A X) (upperStar A g)
    (comparisonUpperStar A U) (openImmersionLowerShriek A j) (upperStar A gU)
    (openImmersionLowerShriek A j') (Etale.upperStar A gU) (comparisonUpperStar A U')
    (Etale.upperStar A g) (comparisonUpperStar A X') (Etale.openImmersionLowerShriek A j')
    q1 q2 q3 q4 q5 q6 (fixSiteOpenExchangeSheaf Λ sq)
  have he := derivedPlusFace
    (Etale.openImmersionLowerShriek A j) (Etale.upperStar A g)
    (Etale.upperStar A gU) (Etale.openImmersionLowerShriek A j') q5 K
  have hx := NatTrans.congr_app hc (DerivedCategory.Plus.ι.obj K)
  dsimp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app] at hx
  change _ = _ at hx
  rw [show DerivedCategory.Plus.ι.map
      ((Etale.extensionZeroBaseChangeDerivedPlusIso Λ hp).hom.app K) =
      (derivedFace (Etale.openImmersionLowerShriek A j) (Etale.upperStar A g)
        (Etale.upperStar A gU) (Etale.openImmersionLowerShriek A j') q5).hom.app
          (DerivedCategory.Plus.ι.obj K) from he]
  exact hx

end AlgebraicGeometry.ProEtale
