/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Composition and boundary dualizing objects on the comparison class

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
cor-weil-boundary-duality-discharge.md, first proof paragraph
(blueprint: lem-weil-boundary-dualizing-composition).

All comparison data below are constructed from the existing compact-support composition,
its actual adjunctions, and the site-comparison unit. No pro-etale ambient adjunction is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Restrict the actual ambient right adjoint to bounded below objects.
Source: the boundary-duality proof, preparation and restriction of adjoints
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryUpperShriekPlus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  _root_.DerivedCategory.TStructure.t.plus.lift
    (_root_.DerivedCategory.Plus.ι ⋙ rightDerivedUpperShriek Λ f)
    (fun K ↦ plus_rightDerivedUpperShriek_obj Λ f K.obj K.property)

/-- The site unit, after applying f-times and ν_X^*, gives ρ_H (also λ_W at A).
Source: boundary-duality proof, explicit comparison-unit transport
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryOriginIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        ((rightDerivedUpperShriek Λ f).obj H.obj) ≅
      (ProEtale.rightDerivedUpperShriek Λ f).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj H.obj) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.mapIso
    ((rightDerivedUpperShriek Λ f).mapIso
      (@asIso _ _ _ _
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app H.obj)
        (ProEtale.isIso_derivedComparisonAdjunction_unit_app
          (ModuleCat.{u + 1} Λ) Y H.obj H.property)))

/-- The constant coefficient object in degree zero, in D+.
Source: boundary-duality proof, evaluation at A
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryCoefficientPlus (S : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨constantComplex Λ S, ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
    (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩⟩

/-- λ_W, including the canonical identification of the pulled-back coefficient unit.
Source: boundary-duality proof, comparison-unit formula for lambda
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryDualizingComparisonIso {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        (dualizingComplex Λ a) ≅
      (ProEtale.rightDerivedUpperShriek Λ a).obj (𝟙_ _) :=
  boundaryOriginIso Λ a (boundaryCoefficientPlus Λ S) ≪≫
    (ProEtale.rightDerivedUpperShriek Λ a).mapIso
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategory.mapIso
          (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} Λ) S).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso
          (ProEtale.comparisonUpperStarUnitIso Λ S) ≪≫
        _root_.DerivedCategory.singleFunctorObjUnitIso _)

end AlgebraicGeometry.Etale
