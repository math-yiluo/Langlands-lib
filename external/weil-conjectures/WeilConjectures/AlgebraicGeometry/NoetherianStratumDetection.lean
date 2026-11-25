/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

set_option linter.privateModule false

/-!
# Detection by pro-etale covers of finitely many locally closed strata

Source: Stacks Project, Tags 09AH and 09AB, followed by finite-stratum induction
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def modelSheafEquivalence (X : Scheme.{u})
    (D : Type*) [Category.{u + 1} D] :
    Sheaf (proEtaleModelTopology X) D ≌ Sheaf (ProEt.topology X) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      D (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      D (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)

@[irreducible] private noncomputable def modelAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type*) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :
    (modelSheafEquivalence Y D).functor ⋙ proEtaleSheafInverseImage f D ⋙
      (modelSheafEquivalence X D).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous D
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f D).restrictFullyFaithful
    (modelSheafEquivalence Y D).fullyFaithfulFunctor
    (modelSheafEquivalence X D).fullyFaithfulFunctor (Iso.refl _) (Iso.refl _)

/-- The ordinary localization at quasi-isomorphisms for modules over any ring sheaf.
Source: Stacks, Tag 05RU (auxiliary; not a blueprint node). -/
noncomputable instance proEtaleAllRingModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    HasDerivedCategory (ringedSiteModules.{u + 1} R) :=
  HasDerivedCategory.standard _

end AlgebraicGeometry.Scheme
