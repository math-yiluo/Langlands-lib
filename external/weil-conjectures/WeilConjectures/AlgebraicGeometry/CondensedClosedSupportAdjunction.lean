/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!
# Closed support for arbitrary condensed coefficients

Source: blueprint `sec-smooth-purity/sk-prop-sf-localization`,
`sk-lem-formal-closed-support-adjunction.md` and its proof
(blueprint: lemma-sections-support-closed-subscheme).

Inverse image uses the canonical coefficient isomorphism and restriction of scalars along
its inverse. This works for noncommutative rings as well. The finite constant-coefficient
kernel construction is generalized to these coefficients, with the same module operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- The existing category of left module objects over the pulled-back ring.
Source: blueprint opening paragraph (blueprint: lemma-sections-support-closed-subscheme).
This is the ring-object presentation of module sheaves, with sectionwise linear maps. -/
abbrev supportModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- Grothendieck structure for arbitrary left modules, without commutativity.
Source: blueprint proof Step 6 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable instance supportModules_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (supportModules Λ X) :=
  Mod.isGrothendieckAbelian.{u + 1, u + 1, u + 2} (condensedRingObj Λ X)

/-- Canonical inverse image, transporting the action through the inverse of alpha.
Source: blueprint proof Steps 1--2 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def supportPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportModules Λ Y ⥤ supportModules Λ X :=
  (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
    Mod.comap (asIso (condensedPullbackHom Λ f)).inv

/-- Exactness and additivity are inherited from inverse image and scalar transport.
Source: blueprint proof Step 2 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable instance supportPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (supportPullback Λ f).Additive := inferInstanceAs
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
        Mod.comap (asIso (condensedPullbackHom Λ f)).inv).Additive)

/-- Inverse image preserves finite limits.
Source: blueprint proof Step 2 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable instance supportPullback_leftExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (supportPullback Λ f) := by
  unfold supportPullback
  infer_instance

/-- Inverse image preserves finite colimits.
Source: blueprint proof Step 2 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable instance supportPullback_rightExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (supportPullback Λ f) := by
  unfold supportPullback
  infer_instance

/-- Scalar transport equivalence along alpha. Both functors restrict scalars.
Source: blueprint proof Step 1 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def supportCoefficientEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)) ≌
        supportModules Λ X :=
  CategoryTheory.Equivalence.mk (Mod.comap (asIso (condensedPullbackHom Λ f)).inv)
    (Mod.comap (condensedPullbackHom Λ f))
    ((Mod.comapId _).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapComp (condensedPullbackHom Λ f) (asIso (condensedPullbackHom Λ f)).inv)
    ((Mod.comapComp (asIso (condensedPullbackHom Λ f)).inv
      (condensedPullbackHom Λ f)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId _)

/-- Canonical module inverse/direct-image adjunction, including its specified unit.
Source: blueprint proof Step 2 (blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable def supportPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportPullback Λ f ⊣ lowerStar Λ f :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)).comp (supportCoefficientEquivalence Λ f).toAdjunction).ofNatIsoRight
      ((Functor.associator _ _ _).symm ≪≫ comapPullbackHomCompIso Λ f)

end AlgebraicGeometry.ProEtale.CondensedRing
