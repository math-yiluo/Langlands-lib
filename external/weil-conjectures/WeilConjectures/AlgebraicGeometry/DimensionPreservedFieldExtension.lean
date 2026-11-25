/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Dimension of an affine spectrum under field extension

Source: Stacks Project, Algebra, Lemma 10.116.5 (Tag 00P3)
(blueprint: lem-weil-pbc-dimension-preserved-field-extension).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Scalar extension preserves the topological Krull dimension of an affine spectrum.
Source: Stacks Project, Algebra, Lemma 10.116.5 (Tag 00P3)
(blueprint: lem-weil-pbc-dimension-preserved-field-extension).

Proof (the node's split, using Tags 00P4 and 0B7I):
1. Tensor-factor symmetry induces a homeomorphism between the spectra of `K ⊗[k] S`
   and `S ⊗[k] K`. Global topological Krull dimension is invariant under this
   homeomorphism, so work in the latter factor order.
2. By `lem-weil-pbc-field-extension-base-change-faithfully-flat`, the map from `S`
   to `S ⊗[k] K` is faithfully flat. By
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`, contraction along this map is
   surjective on prime spectra: every prime of `S` has a prime above it.
3. For each prime of `S ⊗[k] K`, apply
   `lem-weil-pbc-dimension-at-point-field-extension` (00P4) directly. Its local
   dimension equals that at the contracted prime of `S`.
4. By `lem-weil-pbc-dimension-supremum-local-dimensions` (0B7I), each global dimension
   is the supremum of its local dimensions. Surjectivity from step 2 and equality
   from step 3 identify these suprema. The empty spectrum has supremum `⊥`, so the
   zero algebra is included as well.
-/
theorem topologicalKrullDim_spec_tensorProduct_of_field_extension
    (k : Type u) (K : Type v) (S : Type w) [Field k] [Field K] [CommRing S]
    [Algebra k K] [Algebra k S] [Algebra.FiniteType k S] :
    topologicalKrullDim (Spec (CommRingCat.of (K ⊗[k] S))) =
      topologicalKrullDim (Spec (CommRingCat.of S)) := by
  let e := PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k K S).toRingEquiv
  change topologicalKrullDim (PrimeSpectrum (K ⊗[k] S)) =
    topologicalKrullDim (PrimeSpectrum S)
  rw [IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph]
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt,
    topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  have hsurj : Function.Surjective
      (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K))) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  calc
    (⨆ q : PrimeSpectrum (S ⊗[k] K), topologicalKrullDimAt q) =
        ⨆ q : PrimeSpectrum (S ⊗[k] K), topologicalKrullDimAt
          (PrimeSpectrum.comap
            (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K)) q) :=
      iSup_congr fun q ↦ (topologicalKrullDimAt_spec_tensorProduct_field_extension q).symm
    _ = ⨆ q : PrimeSpectrum S, topologicalKrullDimAt q :=
      hsurj.iSup_comp topologicalKrullDimAt

end AlgebraicGeometry
