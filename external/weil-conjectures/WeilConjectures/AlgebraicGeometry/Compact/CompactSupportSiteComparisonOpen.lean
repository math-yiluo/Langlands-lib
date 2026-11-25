/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportProperFactor
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportOpenFactor
import WeilConjectures.AlgebraicGeometry.Open.OpenSiteEvaluationCounit
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.Compactification.RefinementCategory

/-! # Compactified site comparison and open restriction

Source: Stacks Project, proetale.tex, Tags 09A6 and 09AF; canonical mate pasting
(blueprint: lem-amb-compact-support-site-comparison-open).
The coefficient category is the canonical fixed-scalar presentation of ordinary
constant-ring modules. All operations are ordinary and are restricted to D+.

## Main definitions and statements

- `compactSupportEtaleExchangePlus`, `compactSupportProEtaleExchangePlus`: the two actual
  proper-exchange followed by inverse open-extension-exchange maps.
- `compactSupportSiteComparison_open`: their compatibility with the canonical comparison.
- `compactSupportSiteComparison_open_counits`: the direct-image and evaluation normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The site factors used in J preserve the actual proper and open-evaluation counits.
The same assertion for the restricted compactification is obtained by applying this
statement to c.ofIsPullback sq. Source: Stacks Tags 09A6 and 09AF
(blueprint: lem-amb-compact-support-site-comparison-open).

Proof: step 7 of the node. The proper equation is the defining counit-mate identity
of lem-weil-pbc-comparison-direct-image-canonical-mate. For the open equation,
transpose under the open adjunction: the inverse comparison is normalized by the
etale unit and pullback comparison as in lem-fix-site-open-exchange. Naturality and
the etale triangle identity make its transpose the pullback comparison. The
pro-etale triangle identity gives the same transpose for the evaluation composite.
The adjunction Hom bijection is injective, proving the displayed equation. -/
theorem compactSupportSiteComparison_open_counits
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    {f : X ⟶ S} (c : Compactification f) [IsNoetherian c.Z] :
    (∀ K : DerivedCategory.Plus (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (fixedComparisonPullbackPlus A c.g).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) c.g).obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) c.g).mapDerivedCategoryPlus.map
          ((fixedComparisonDirectImageMatePlus A c.g).app K) ≫
        (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c.g).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.obj K) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c.g).counit.app K)) ∧
    (∀ B : DerivedCategory.Plus (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlusAdjunction.counit.app B) =
        (properOpenSiteExtensionIso A c.i).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj B) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus A c.i).hom.app B) ≫
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlusAdjunction.counit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.obj B)) := by
  constructor
  · intro K
    exact fixedComparisonDirectImageMatePlus_counit A c.g K
  · exact openSiteEvaluationCounit A c.i

end AlgebraicGeometry.ProEtale
