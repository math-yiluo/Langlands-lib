/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitFaithful
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The extension-by-zero/restriction unit is monic.
Source: Stacks Project, Sheaves Lemma 00A7 (4).
Proof: identify sections on opens contained in W with the unique direct-sum summand;
the resulting restriction map is injective, and sheafification preserves this comparison.
(blueprint: lem-sc-module-extension-by-zero-unit-mono) -/
theorem moduleExtensionByZero_unit_mono (X : RingedSpace.{u}) (W : Opens X)
    (G : SheafOfModules.{u} ((moduleRings X).over W)) :
    Mono ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G) := by
  let adj := Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2
  let : (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).Faithful :=
    extensionByZero_faithful X W
  exact adj.unit_mono_of_L_faithful G
end AlgebraicGeometry
