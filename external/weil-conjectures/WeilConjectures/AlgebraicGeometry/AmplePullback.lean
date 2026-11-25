/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback

/-! # Pullback of an ample invertible module

Source: Stacks Project, Morphisms, Lemma 0892, part (2)
(blueprint: lem-weil-pbc-pullback-ample-invertible).
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- An affine pullback preserves ampleness.
Source: Stacks Project, Morphisms, Lemma 0892, part (2), specialized to an affine
morphism; the affine nonvanishing-locus criterion is Properties Definition 01PS
(blueprint: lem-weil-pbc-pullback-ample-invertible).
Proof, following the node's two steps:
1. The pullback is invertible and commutes with tensor powers by
`lem-weil-pbc-invertible-pullback-tensor`. Its fibre formula sends a section value to
that value tensored with one. Extension of residue fields preserves nonzero vectors,
so the pulled-back nonvanishing locus is the inverse image of the original locus.
2. By `hL` and `def-weil-pbc-ample-invertible-module`, `X` is quasi-compact and is
covered by affine nonvanishing loci of positive tensor powers. Choose a finite cover.
Its inverse images cover `Y` and are affine by clauses (1) and (2) of
`lem-weil-pbc-affine-morphism-permanence`. Each is quasi-compact by
`lem-weil-pbc-affine-scheme-qcqs`; their finite union is quasi-compact. These loci
therefore satisfy the same ampleness criterion on `Y`.
-/
theorem isAmple_tensorPullback_of_isAffineHom {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsAffineHom g] (L : X.Modules) [L.IsInvertible] (hL : IsAmple X L) :
    @IsAmple Y ((tensorPullback g).obj L) ((invertible_pullback_tensor g).1 L).2 := by
  have : CompactSpace X := hL.1
  refine ⟨QuasiCompact.compactSpace_of_compactSpace g, ?_⟩
  intro y
  obtain ⟨n, hn, s, U, hy, hU, hUs⟩ := hL.2 (g y)
  obtain ⟨t, ht⟩ := exists_tensorPow_section_nonvanishing_pullback g L n hn s
  refine ⟨n, hn, t, g ⁻¹ᵁ U, hy, hU.preimage g, ?_⟩
  intro z
  change g z ∈ U ↔ z ∈ nonvanishingLocus _ t
  rw [ht]
  exact hUs (g z)

end AlgebraicGeometry.Scheme.Modules
