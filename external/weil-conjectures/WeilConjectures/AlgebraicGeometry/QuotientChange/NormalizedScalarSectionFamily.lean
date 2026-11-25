/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
import WeilConjectures.AlgebraicGeometry.SectionPullNormalizationTransport

/-! # Simultaneous normalized scalar section comparisons

## References

* Stacks Project, Tags 03EK, 0D6D, 07A6 and 0E47
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

/-- Normalized scalar realization data can be fixed simultaneously, and every
universally normalized internal pull comparison has a section-normalized realization
using that same family. This assertion concerns pullbacks only. -/
theorem normalized_scalar_section_family (φ : Λ ⟶ Λ') [IsMonHom φ]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (normalized : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized φ h (b h)) :
    ∃ s : ∀ T : Scheme.{u}, SectionScalarComparison φ T,
      (∀ T : Scheme.{u}, SectionScalarNormalized φ T (s T)) ∧
      ∀ {U V : Scheme.{u}} (h : U ⟶ V),
        SectionPullNormalized φ h (s U) (s V) (b h) := by
  classical
  have exists_section (T : Scheme.{u}) :
      ∃ s : SectionScalarComparison φ T, SectionScalarNormalized φ T s := by
    obtain ⟨tX, tY, e, sX, sY, htX, htY, he, hsX, hsY, hTX, hTY, hp⟩ :=
      internal_scalar_pullback_normalization φ (𝟙 T)
    exact ⟨sX, hsX⟩
  choose s hs using exists_section
  exact ⟨s, hs, fun h ↦ section_pull_normalized_of_normalized φ h
    _ _ (hs _) (hs _) (b h) (normalized h)⟩

end AlgebraicGeometry.ProEtale.QuotientChange
