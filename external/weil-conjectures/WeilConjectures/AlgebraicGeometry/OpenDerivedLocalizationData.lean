/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Derived categories on an open subscheme

For an open `U` of `X`, derived categories of `𝒪_U`-modules and of modules on the localized
sites of `U`, in the universe of the derived categories given on `X`.
Source: Stacks Project, Tag 079W.
(blueprint: lem-pc-open-derived-localization-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Derived categories of `𝒪_U`-modules and of the modules on the localized sites of `U` exist
in the universe `w` of the given derived categories over the localized sites of `X`.
The first is transported along `Scheme.Modules.overEquiv U`, the second is
`nonempty_derivedOpenLocalization`. -/
theorem open_derived_localization_data (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) :
    ∃ hD : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
    letI := hD
    Nonempty (∀ W : U.toScheme.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W))) := by
  classical
  let B := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  have hD : Nonempty (HasDerivedCategory.{w} D) := by
    let : HasDerivedCategory.{u + 1} D := HasDerivedCategory.standard D
    let e : B ≌ D := Scheme.Modules.overEquiv U
    let ed := e.mapDerivedCategory
    let : LocallySmall.{w} (DerivedCategory D) :=
      (locallySmall_congr ed).mp inferInstance
    exact ⟨(HomologicalComplex.quasiIso D (.up ℤ)).hasLocalizationOfLocallySmall
      DerivedCategory.Q⟩
  obtain ⟨hD⟩ := hD
  let := hD
  exact ⟨hD, nonempty_derivedOpenLocalization U.toScheme⟩

end AlgebraicGeometry
