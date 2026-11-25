/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Projection formula locality: global to local

If the projection-formula map is an isomorphism, it stays an isomorphism after restriction
to every open (Stacks Project, Lemma 36.22.1, Tag 08EU). -/

@[expose] public section
universe u w v
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
set_option autoImplicit false
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
/-- A global isomorphism remains an isomorphism after every open restriction.
Source: Stacks Project, perfect.tex, Lemma 36.22.1 (Tag 08EU).
(blueprint: lem-pc-projection-locality-global-to-local)
The restriction functor preserves isomorphisms. -/
theorem projectionFormula_global_to_local
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : schemeDerivedCategory X) (K : schemeDerivedCategory Y)
    (I : Type v) (U : I → Y.Opens)
    (φ : ((schemeDerivedDirectImage f).obj E) ⊗ K ⟶
      (schemeDerivedDirectImage f).obj (E ⊗ ((derivedPullback f).obj K))) :
    IsIso φ → ∀ i : I,
      IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ) := by
  intro h i
  exact Functor.map_isIso (schemeOpenRestriction Y (U i)).mapDerivedCategory φ
end AlgebraicGeometry
