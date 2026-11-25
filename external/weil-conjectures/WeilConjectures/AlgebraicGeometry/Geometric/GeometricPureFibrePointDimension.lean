/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Fibre.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension

set_option linter.privateModule false

/-! # Pointwise dimension from pure geometric fibres

Source: Stacks Project, Algebra, Tag 00P4; Morphisms, Tag 02FY (1);
Varieties, Tag 0A21 (3), (5)
(blueprint: lem-trf-geometric-pure-fibre-point-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Transport local dimension by identifying the open neighbourhoods of a homeomorphism.
private theorem localDim_homeomorph_le {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hx).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq eV eV.isHomeomorph)

private theorem localDim_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e x) := by
  exact le_antisymm (localDim_homeomorph_le e x)
    (by simpa using localDim_homeomorph_le e.symm (e x))

-- Over a one-point base the fibre inclusion is a surjective embedding.
private theorem localDim_asFiber_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    topologicalKrullDimAt (f.asFiber x) = topologicalKrullDimAt x := by
  have hsurj : Function.Surjective (f.fiberι (f x)) := by
    intro y
    exact ⟨(f.fiberHomeo (f x)).symm ⟨y, Subsingleton.elim _ _⟩,
      f.fiberι_fiberHomeo_symm _ _⟩
  have he := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(f.fiberι (f x)).isEmbedding, hsurj⟩
  simpa using localDim_homeomorph (he.homeomorph _) (f.asFiber x)

-- Pass purity to the subtype of the top open, as required by the open-dimension API.
end AlgebraicGeometry
