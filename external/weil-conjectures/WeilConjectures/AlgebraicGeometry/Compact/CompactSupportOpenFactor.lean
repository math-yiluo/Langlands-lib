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
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.AlgebraicGeometry.SmoothPurity.FixSiteOpenExchange
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

/-! # The open site-comparison factor

Source: Stacks Project, Tags 09A6, 09AF and 099R; the factor calculation in
lem-amb-compact-support-site-comparison-open
(blueprint: lem-amb-compact-support-open-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem inclusion_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem inclusion_comp_inv {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K)).inv =
      ((Functor.mapDerivedCategoryCompIso F G).symm.app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem pro_square_conjugate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {h : Z' ⟶ Z} (sq : CommSq v j' j h) :
    conjugateIsoEquiv
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j'))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v))
      (upperStarCompIso (ModuleCat.{u + 1} A) sq.w) =
      squareLowerStarIso (ModuleCat.{u + 1} A) sq := by
  dsimp only [upperStarCompIso, squareLowerStarIso]
  rw [conjugateIsoEquiv_trans _
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (v ≫ j)) _,
    conjugateIsoEquiv_trans _
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (j' ≫ h)) _,
    conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarComp]
  simp only [Iso.trans_assoc]
  congr 2
end AlgebraicGeometry.ProEtale
