/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Ring data for affine charts in flatness descent

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph.
(blueprint: def-weil-pbc-flat-descent-chart).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The ring data of one affine triple in the proof of Stacks Tag 04AI.
(blueprint: def-weil-pbc-flat-descent-chart). -/
structure FlatDescentChart (J : Type u) [Preorder J] (j₀ : J) where
  rings : J ⥤ CommRingCat.{u}
  source : CommRingCat.{u}
  target : CommRingCat.{u}
  sourceAlgebra : Algebra (rings.obj j₀) source
  targetAlgebra : Algebra (rings.obj j₀) target
  map : letI := sourceAlgebra; letI := targetAlgebra; source →ₐ[rings.obj j₀] target
  finitePresentation : map.toRingHom.FinitePresentation

namespace FlatDescentChart

/-- Flatness of the chart's tensor-product map after an arbitrary base-ring map. 
(blueprint: def-weil-pbc-flat-descent-chart)
-/
def baseFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    {R : CommRingCat.{u}} (q : a.rings.obj j₀ ⟶ R) : Prop :=
  letI := a.sourceAlgebra
  letI := a.targetAlgebra
  letI := q.hom.toAlgebra
  (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom.Flat

/-- Flatness of a chart at a stage above its initial stage. 
(blueprint: def-weil-pbc-flat-descent-chart)
-/
def stageFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    (j : J) (h : j₀ ≤ j) : Prop :=
  a.baseFlat (a.rings.map (homOfLE h))

/-- Flatness of the chart over the colimit of its base rings. 
(blueprint: def-weil-pbc-flat-descent-chart)
-/
def limitFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀) : Prop :=
  a.baseFlat (colimit.ι a.rings j₀)

end FlatDescentChart

end AlgebraicGeometry
