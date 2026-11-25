/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Small.Basic

/-! # Smallness of perfect isomorphism classes on an open

Source: the induction property in the proof of
lem-pc-perfect-complexes-compact-set, using Stacks Project, Tag 08DR
(blueprint: def-pc-perfect-classes-small-on-open).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The perfect quasi-coherent derived objects on an open have `u`-small isomorphism
classes. Quantifying over open immersions with this image avoids identifying a scheme
with its top open subscheme. The quantification over derived-category structures lets
the induction property be stated before choosing structures on the open subschemes.
Source: the property `P(W)` in Step 2 of lem-pc-perfect-complexes-compact-set;
Stacks Project, Tag 08DR (blueprint: def-pc-perfect-classes-small-on-open). -/
def PerfectComplexClassesSmallOnOpen (X : Scheme.{u}) (U : X.Opens) : Prop :=
  ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [IsOpenImmersion f], f.opensRange = U →
    ∀ [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      [∀ V : Y.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))],
      Small.{u} (Skeleton (ObjectProperty.FullSubcategory
        (fun E : schemeDerivedQCohCategory Y ↦ IsPerfect Y E.obj)))

end AlgebraicGeometry.Scheme
