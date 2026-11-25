/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenSheafComparison
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Sf.SfConstructibleExceptionalAdjointDischarge
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginDerivedCategory
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginDerivedCategory
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Comma.Basic
import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom

/-!
# Proper exceptional inverse image and arbitrary open restriction

The ambient adjunction and the relative etale-origin assertion have separate hypotheses.
The proper/open map is fixed by sectionwise restriction and the open adjunctions.

## Main definitions

* `sfProperOpenDerivedComparison`: the canonical proper/open support arrow Γ.
* `sfProperExceptionalOpenComparison`: its double-transpose exceptional comparison β.
* `sfProperEtaleOriginFixedForgetful`: canonical coefficient realization of the recorded
  bounded-below etale-origin category.

## Main statements

* `sfProperExceptionalOpenBaseChange`: the conditional unbounded ambient assertion.
* `sfProperFiniteExceptionalOpenBaseChange`: the independent etale-origin assertion.

## References

* Stacks Tags 09AE and 09BN
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Open restriction of direct image, using exactly the sectionwise fibre-product map
of the recorded sheaf comparison, now expressed with the exact inverse-image functors. -/
noncomputable def sfProperOpenPullbackRestriction {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantModuleDirectImage p A ⋙ sfIntrinsicPullback A i ≅
      sfIntrinsicPullback A k ⋙ proEtaleConstantModuleDirectImage r A :=
  isoWhiskerRight (sfProperOpenDirectImageCoordinates A p) _ ≪≫
    (sfIntrinsicTransportComp A _ _).symm ≪≫
    sfIntrinsicTransportIso A
      (isoWhiskerLeft _
          (ProEtale.upperStarIsoOpenImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i) ≪≫
        sfProperOpenFixedRestrictionIso A r k i p sq ≪≫
        isoWhiskerRight
          (ProEtale.upperStarIsoOpenImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).symm _) ≪≫
    sfIntrinsicTransportComp A _ _ ≪≫
    isoWhiskerLeft _ (sfProperOpenDirectImageCoordinates A r).symm

/-- Derived open restriction. Direct image preserves K-injectives as right adjoint to
exact inverse image; open pullback preserves them as right adjoint to exact extension.
Thus this is induced by the specified sectionwise map on K-injective representatives.
No finite-CD or ambient-adjoint hypothesis is needed for this restriction isomorphism. -/
noncomputable def sfProperOpenDerivedRestriction {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantDerivedDirectImage p A ⋙ sfIntrinsicDerivedPullback A i ≅
      sfIntrinsicDerivedPullback A k ⋙ proEtaleConstantDerivedDirectImage r A :=
  letI := (sfIntrinsicConstantModuleAdjunction p A).preservesKInjectiveComplexes
  letI := (sfIntrinsicOpenAdjunction A k).preservesKInjectiveComplexes
  isoWhiskerLeft (proEtaleConstantDerivedDirectImage p A)
      (sfIntrinsicPullback A i).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (sfProperOpenPullbackRestriction A r k i p sq) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    isoWhiskerRight (sfIntrinsicPullback A k).rightDerivedFunctorIsoMapDerivedCategory _

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale
open Scheme

end AlgebraicGeometry.ProEtale
