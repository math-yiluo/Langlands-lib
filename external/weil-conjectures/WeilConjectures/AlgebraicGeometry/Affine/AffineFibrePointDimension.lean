/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents

set_option linter.privateModule false

/-! # Affine fibre charts and dimension at their marked points

Source: Stacks Project, Schemes, Tags 01JQ, 01JR and 01J9; Algebra, Tags 05G3 and
00OT; Topology, Tag 0055 (blueprint: lem-trf-affine-fibre-point-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem localDim_homeomorph_le {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (i : Y ≃ₜ Z) (y : Y) :
    topologicalKrullDimAt y ≤ topologicalKrullDimAt (i y) := by
  refine le_iInf₂ fun O hy ↦ ?_
  let V : TopologicalSpace.Opens Y := ⟨i ⁻¹' O, O.isOpen.preimage i.continuous⟩
  let iV : V ≃ₜ O := i.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hy).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq iV iV.isHomeomorph)

private theorem localDim_openImmersion {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] (y : Y) : topologicalKrullDimAt y = topologicalKrullDimAt (j y) := by
  let i := j.isOpenEmbedding.toHomeomorph
  have he : topologicalKrullDimAt y = topologicalKrullDimAt (i y) :=
    le_antisymm (localDim_homeomorph_le i y)
      (by simpa using localDim_homeomorph_le i.symm (i y))
  exact he.trans (j.isOpenEmbedding.isOpen_range.topologicalKrullDimAt_eq ⟨y, rfl⟩)

end AlgebraicGeometry
