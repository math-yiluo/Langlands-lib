/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicSiteHomTransportChain
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-! # Representative-level intrinsic Hom transport

## References

* Stacks Project, Tags 00YV, 08J7 and 0A95
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

set_option linter.style.haveILetI false

/-- Representative-level coefficient transport, for fixed representatives `Lc` and `Ic` of the
source and target derived objects with `Ic` K-injective. -/
theorem intrinsicSiteHom_transport_representatives (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (Lc Ic : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [Ic.IsKInjective] :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
            (op (DerivedCategory.Q.obj Lc))).obj (DerivedCategory.Q.obj Ic)) ≅
        (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
          (proEtaleConstantRing X A)).obj
          (op ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
            (DerivedCategory.Q.obj Lc)),
            (finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
              (DerivedCategory.Q.obj Ic))) := by
  let F := finiteCoefficientIntrinsicRealization X A
  letI : F.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact X A).1
  letI : F.PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_isEquivalence F
  obtain ⟨e₁⟩ := intrinsicSiteHom_transport_chain X A Lc Ic
  obtain ⟨e₂⟩ := derivedInternalHomOfUniverses_obj_iso.{u + 1, u, u}
    (ProEt.topology X) (proEtaleConstantRing X A)
    (F.mapDerivedCategory.obj (DerivedCategory.Q.obj Lc))
    (F.mapDerivedCategory.obj (DerivedCategory.Q.obj Ic))
    ((F.mapHomologicalComplex (.up ℤ)).obj Lc)
    ((F.mapHomologicalComplex (.up ℤ)).obj Ic)
    (F.mapDerivedCategoryFactors.app Lc).symm
    (F.mapDerivedCategoryFactors.app Ic).symm
  exact ⟨e₁ ≪≫ e₂.symm⟩

end AlgebraicGeometry.ProEtale
