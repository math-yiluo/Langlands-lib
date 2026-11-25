/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-!
# Composition of derived direct images

Source: literature/stacks-project/cohomology.tex, Lemma 20.28.2 (Tag 0D5T),
Cohomology of unbounded complexes (blueprint: lem-pc-derived-direct-image-composition).

This module states the canonical composition comparison for the unbounded derived direct
image of morphisms of schemes.
-/

@[expose] public section

universe u₂ wX₂ wY₂ wZ₂

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u₂}}
  [HasDerivedCategory.{wX₂} (SheafOfModules.{u₂} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{wY₂} (SheafOfModules.{u₂} (moduleRings Y.toRingedSpace))]
  [HasDerivedCategory.{wZ₂} (SheafOfModules.{u₂} (moduleRings Z.toRingedSpace))]

/-- The derived direct image of a composite is canonically naturally isomorphic to the
composite of the derived direct images. Source: Stacks Project, Lemma 20.28.2 (Tag 0D5T),
using the derived pullback composition and uniqueness of right adjoints
(blueprint: lem-pc-derived-direct-image-composition). -/
theorem derivedDirectImageComposition (p : X ⟶ Y) (f : Y ⟶ Z) :
    Nonempty
      (schemeDerivedDirectImage (p ≫ f) ≅
        schemeDerivedDirectImage p ⋙ schemeDerivedDirectImage f) := by
  obtain ⟨e, _⟩ := RingedSpace.exists_derivedModuleDirectImageComposition
    p.toLRSHom.toShHom f.toLRSHom.toShHom
  exact ⟨e.symm⟩

end AlgebraicGeometry
