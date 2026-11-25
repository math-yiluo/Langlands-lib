/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
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
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicSiteHomTransportRepresentatives
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-! # Internal Hom in the intrinsic finite-coefficient presentation

## References

* Stacks Project, Tags 00YV, 08J7 and 0A95
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Constant-scalar realization identifies the two ambient derived internal Homs.
There are no geometric finiteness or constructibility hypotheses. -/
theorem intrinsicSiteHom_transport (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (K L : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj (op K)).obj L) ≅
        (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
          (proEtaleConstantRing X A)).obj
          (op ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj K),
            (finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj L))  := by
  let C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let F := finiteCoefficientIntrinsicRealization X A
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let Lc := DerivedCategory.Q.objPreimage K
  let Mc := DerivedCategory.Q.objPreimage L
  obtain ⟨Ic, hIc, j, _, hj⟩ :=
    Abelian.HasKInjectiveResolutions.exists_isKInjective Mc
  letI := hIc
  letI := hj
  let eK : DerivedCategory.Q.obj Lc ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eL : DerivedCategory.Q.obj Ic ≅ L :=
    (asIso (DerivedCategory.Q.map j)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L
  obtain ⟨e⟩ := intrinsicSiteHom_transport_representatives X A Lc Ic
  let eK' := F.mapDerivedCategory.mapIso eK
  let eL' := F.mapDerivedCategory.mapIso eL
  let a := (derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapIso eK.op
  let b := ((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
    (op (DerivedCategory.Q.obj Lc))).mapIso eL.symm
  exact ⟨F.mapDerivedCategory.mapIso (a.app L ≪≫ b) ≪≫ e ≪≫
    (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
      (proEtaleConstantRing X A)).mapIso (eK'.symm.op.prod eL')⟩

end AlgebraicGeometry.ProEtale
