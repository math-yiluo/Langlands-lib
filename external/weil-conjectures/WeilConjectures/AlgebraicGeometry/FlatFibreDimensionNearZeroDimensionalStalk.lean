/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.RestrictedFibreCohenMacaulayLocus
import WeilConjectures.AlgebraicGeometry.CohenMacaulayFibreDimensionDecomposition
import WeilConjectures.RingTheory.DepthLeSupportDimension

/-! # Constant fibre dimension near a zero-dimensional fibre stalk

Source: Stacks Project, Tags 045U, 02NM and 02NJ.
(blueprint: lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A zero-dimensional fibre stalk has a neighbourhood of constant fibre dimension.

The local ring dimension at x is zero, whereas the local *topological* dimension of
the fibre near x is n. These numbers need not agree: at the generic point of an
affine line they are zero and one, respectively.

Source: Stacks Project, Tags 045U (openness), 02NM (relative dimension decomposition),
and 02NJ (equidimensional fibres).
Proof: Restrict f over U. Identify its fibre at f(x) with the original fibre, using
the pullback square for restriction and the residue-field isomorphism at a point
of an open subscheme. This identifies the fibre stalk at x with the given stalk.
The fibre is locally of finite type over a field, hence locally Noetherian. Its
local ring at x has depth at most its Krull dimension by the depth-support bound.
Its dimension is zero and depth is nonnegative, so its depth equals its dimension;
thus this Noetherian local ring is Cohen-Macaulay. By Tag 045U the Cohen-Macaulay locus is
open. Restrict to that locus; the resulting morphism is flat, locally finitely
presented and has Cohen-Macaulay fibres. Tag 02NM decomposes this locus into open
and closed pieces of relative dimension n. Take the piece containing x, and map
it into X by the two open restriction inclusions, giving V. Its image lies over U.
The fibres of this piece are equidimensional of dimension n by Tag 02NJ. Every
nonempty open neighbourhood in such a fibre has dimension n, so its local
topological dimension at each point is n. The fibre of the piece is an open
subscheme of the original fibre, and local topological dimension is unchanged by
an open embedding. These identifications give the equality for every y in V.
Empty schemes and the empty base open have no x satisfying the hypotheses.
(blueprint: lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk) -/
theorem exists_constant_fibre_dimension_neighbourhood_of_stalk_dimension_zero
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x : X) (hx : f x ∈ U)
    (hdim : ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = 0) :
    ∃ (n : ℕ) (V : X.Opens), x ∈ V ∧
      ∀ y ∈ V, f y ∈ U ∧ topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞) := by
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    isLocallyNoetherian_fibre_of_finite_presentation_restrict f U (f x) hx
  have hdepth :
      (IsLocalRing.depth (R := (f.fiber (f x)).presheaf.stalk (f.asFiber x))
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
    apply le_antisymm
    · simpa only [Module.supportDim_self_eq_ringKrullDim] using
        IsLocalRing.depth_le_supportDim
          (R := (f.fiber (f x)).presheaf.stalk (f.asFiber x))
          ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
    · rw [hdim]
      exact WithBot.coe_le_coe.mpr zero_le
  let W : X.Opens := ⟨_, isOpen_fibre_depth_eq_ringKrullDim_over_restrict f U⟩
  have hxW : x ∈ W := ⟨hx, hdepth⟩
  obtain ⟨V, hcover, _, hV⟩ :=
    exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim f U W
      (fun _ hy => hy)
  have hxcover : x ∈ ⨆ n, V n := hcover.symm ▸ hxW
  obtain ⟨n, hxn⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  refine ⟨n, V n, hxn, fun y hy => ⟨?_, hV n y hy⟩⟩
  have hyW : y ∈ W := hcover ▸ TopologicalSpace.Opens.mem_iSup.mpr ⟨n, hy⟩
  exact hyW.1

end AlgebraicGeometry
