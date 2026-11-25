/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Open pro-etale pullback preserves K-injective complexes

## References

* Stacks Project, Tags 08FI and 09A5
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local irreducible] proEtaleRingModulePullback

/-- Open pullback preserves K-injectives, including transported coefficient rings. -/
@[instance] theorem open_pullback_preservesKInjectiveComplexes {S Z : Scheme.{u}}
    (j : S ⟶ Z) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ R') :
    (proEtaleRingModulePullback j R R' c).PreservesKInjectiveComplexes := by
  let U : Z.ProEt := ProEt.mk j
  have : IsOpenImmersion U.hom := ‹IsOpenImmersion j›
  obtain ⟨q, ⟨hq⟩⟩ := proEtale_ringed_open_comparison U R
  let A := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let F := SheafOfModules.overFunctor.{u + 1} A U
  have : F.Additive := (ringedOverFunctor_exactGeneral A U).1
  have : F.PreservesKInjectiveComplexes := ⟨fun K _ ↦
    isKInjective_restrict_localizedOfUniverses.{u + 1, u, 0} A U inferInstance K⟩
  let e := proEtaleScalarEquivalence S ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  obtain ⟨theta, _, _, htheta⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let p : proEtaleRingModulePullback j R R' c ≅
      proEtaleModuleInverseImage j R ⋙ e.inverse := by
    unfold proEtaleRingModulePullback
    exact NatIso.ofComponents (fun M ↦ theta ((proEtaleModuleInverseImage j R).obj M))
      (fun a ↦ htheta _ _ ((proEtaleModuleInverseImage j R).map a))
  let rq : F ⋙ q.inverse ≅ proEtaleModuleInverseImage j R :=
    Functor.isoWhiskerRight hq.symm q.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ q.unitIso.symm ≪≫ Functor.rightUnitor _
  have : q.inverse.Additive := q.inverse.additive_of_preserves_binary_products
  have : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  have : (proEtaleModuleInverseImage j R).Additive := Functor.additive_of_iso rq
  have : (proEtaleModuleInverseImage j R).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso rq
  have : (proEtaleRingModulePullback j R R' c).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso p.symm
  infer_instance

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
