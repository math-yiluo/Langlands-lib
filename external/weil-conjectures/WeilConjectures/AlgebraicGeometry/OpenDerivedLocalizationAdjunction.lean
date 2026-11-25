/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Derived localizations and the adjunction for open restriction

Source: Stacks Project, Tag 079W, Lemma cohomology-lemma-adjoint.
(blueprint: lem-pc-open-derived-localization-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The module category of an open subscheme `U` has a derived category with Hom types in
universe `w`, transported from the localization over the open `U` of `X`.
Source: Stacks Project, Tag 079W.
(blueprint: lem-pc-open-derived-localization-adjunction).

Proof: form the standard derived category on `U`. The exact canonical module equivalence
`Modules.overEquiv U` induces a derived equivalence with the given localization on the
localized site over `U`, which transports local `w`-smallness to the standard derived
category on `U`; `hasLocalizationOfLocallySmall` then shrinks its Hom types. -/
theorem nonempty_hasDerivedCategory_openSubscheme
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) := by
  let B := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let : HasDerivedCategory.{u + 1} D := HasDerivedCategory.standard D
  let e : B ≌ D := Scheme.Modules.overEquiv U
  let ed := e.mapDerivedCategory
  let : LocallySmall.{w} (DerivedCategory D) :=
    (locallySmall_congr ed).mp inferInstance
  exact ⟨(HomologicalComplex.quasiIso D (.up ℤ)).hasLocalizationOfLocallySmall
    DerivedCategory.Q⟩

/-- Localized restriction to an open `U` has a right adjoint on derived categories.
No support or detector assertion is made.
Source: Stacks Project, Tag 079W, Lemma cohomology-lemma-adjoint, used for the open
inclusion in Tag 0A9A, Lemma perfect-lemma-supported-generator.
(blueprint: lem-pc-open-derived-localization-adjunction).

Proof: the localized restriction functor has its explicit underived right adjoint. The
localized module category is Grothendieck abelian by
`grothendieckAbelian_and_functorial_kInjective_resolutions`, so it has K-injective
resolutions. The upstream `mapDerivedCategoryRightDerivedAdjunction` derives the right
adjoint of exact restriction and supplies the displayed adjunction. This right adjoint is
determined up to natural isomorphism. Empty and full opens use the same construction. -/
theorem open_derived_localization_adjunction
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X),
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R) := by
  classical
  let B := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let : IsGrothendieckAbelian.{u} B :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      ((Opens.grothendieckTopology X).over U) (X.toRingedSpace.sheaf.over U)).1
  let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let : L.IsLeftAdjoint := by dsimp [L, SheafOfModules.overFunctor]; infer_instance
  let G := Functor.rightAdjoint L
  let : G.Additive := Functor.additive_of_preserves_binary_products G
  exact ⟨G.rightDerivedFunctor,
    ⟨(Adjunction.ofIsLeftAdjoint L).mapDerivedCategoryRightDerivedAdjunction⟩⟩

end AlgebraicGeometry
