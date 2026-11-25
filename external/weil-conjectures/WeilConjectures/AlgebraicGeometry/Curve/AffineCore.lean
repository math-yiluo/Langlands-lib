/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The affine core of a smooth curve

A smooth curve `C` over a field which is geometrically connected has a nonempty dense affine
open subscheme whose complement is a finite set of points.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_isAffineOpen_dense_finite_compl`: the affine core of a
  smooth geometrically connected curve.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Affine core of a smooth curve.** A smooth geometrically connected curve `C` over a field
`k₀` has a nonempty dense affine open subscheme `V` whose complement is finite.

The blueprint obtains `V` by removing points from the smooth proper completion of `C`; it is
enough to take any nonempty affine open: `C` is irreducible (connected and regular), so every
nonempty open is dense, and its complement is finite since `C` is a noetherian space of
dimension one. (blueprint: `theorem-weight-bound-curve--1`) -/
theorem IsCurve.exists_isAffineOpen_dense_finite_compl {k₀ : Type u} [Field k₀]
    {C : Scheme.{u}} (p : C ⟶ Spec (.of k₀)) [IsCurve p] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] :
    ∃ V : C.Opens, IsAffineOpen V ∧ (V : Set C).Nonempty ∧ Dense (V : Set C) ∧
      (V : Set C)ᶜ.Finite := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular C := IsRegular.of_smooth p
  have : ConnectedSpace C := GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have hdim : topologicalKrullDim C = 1 :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq p 1).mp inferInstance
  have : CompactSpace C := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  obtain ⟨x⟩ : Nonempty C := inferInstance
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  exact ⟨V, hV, ⟨x, hx⟩, V.isOpen.dense ⟨x, hx⟩,
    V.isOpen.finite_compl_of_topologicalKrullDim_le_one hdim.le ⟨x, hx⟩⟩

end AlgebraicGeometry
