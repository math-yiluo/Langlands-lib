/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction

/-! Derived extension adjunction transported across the over-site equivalence.
Source: Stacks Project, Tags 08BS and 08BT.
(blueprint: lem-pc-open-extension-projection-formula). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable section
universe u w

local instance openExtensionProjectionStandardDerivedAdj (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- The derived extension-by-zero adjunction after transporting the open over-site to `U`.
Source: Stacks Project, Tags 08BS and 08BT.
(blueprint: lem-pc-open-extension-derived-adjunction).
Proof: construct the exact extension-by-zero and restriction adjunction on sheaves,
derive it through the standard localizations, and transport the right adjoint across
the over-site equivalence. The derived adjunction construction then supplies `J` and
its adjunction with `R`; the construction is canonical up to adjunction isomorphism. -/
theorem exists_openExtension_derivedAdjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∃ J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X,
      Nonempty (J ⊣ R) := by
  let e₀ : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv U
  let e := e₀.mapDerivedCategory
  let a₀ := derived_open_shriek_adjunction X.toRingedSpace U
  let a₁ : e.inverse ⊣ e.functor := e.symm.toAdjunction
  exact ⟨_, ⟨a₁.comp a₀.some⟩⟩

end
end AlgebraicGeometry
