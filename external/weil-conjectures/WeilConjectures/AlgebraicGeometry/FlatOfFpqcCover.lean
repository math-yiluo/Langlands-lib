/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Flatness descends along fpqc covering families

Source: Stacks Project, Descent, Lemma Tag 02L2, descent direction of Definition Tag 02KO
(blueprint: lem-weil-pbc-fpqc-descend-flat).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flatness descends along an fpqc covering family. Source: Stacks Project, Descent,
Lemma Tag 02L2 (blueprint: lem-weil-pbc-fpqc-descend-flat).

1. Flatness is invariant under isomorphisms and Zariski local on both source and target:
   the local-ring maps are identified by isomorphisms or restriction to open subschemes
   (`def-weil-flat-morphism`, `def-pc-scheme`).
2. Flatness is stable under base change (`lem-weil-pbc-flat-morphism-base-change`).
3. For a flat surjective map of affine bases, write the map as `Spec` of a ring map.
   The ring map is flat (`lem-weil-pbc-flat-ring-map-iff-flat-affine`) and its map on prime
   spectra is surjective, hence it is faithfully flat
   (`lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`).
4. For each affine open `U = Spec A` of the source, its inverse image is the base change
   of `U` (`lem-weil-pbc-open-preimage-fibre-product`,
   `lem-weil-pbc-cartesian-square-pasting`). It is the spectrum of the tensor product
   (`lem-weil-pbc-fibre-product-affine-spectra`). The flat base-changed morphism therefore
   says that this tensor product is flat over the new base ring, using the affine
   equivalence and the tensor-product swap.
5. Faithfully flat descent of module flatness
   (`lem-weil-pbc-flatness-descends-faithfully-flat`) implies that `A` is flat over the
   original base ring. Thus each affine restriction of the original morphism is flat,
   and source locality implies that the original morphism is flat.
6. Steps 1, 2 and 5 verify the fpqc-local-on-the-base criterion (Tag 02KP). Apply it to the given
   fpqc covering family and the flat second projections to conclude that `f` is flat. -/
theorem flat_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, Flat (pullback.snd f (g i))) : Flat f := by
  apply Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @Flat) ?_ f
    (fun i => pullback.fst f (g i)) (fun i => pullback.snd f (g i))
    (fun i => IsPullback.of_hasPullback f (g i)) h
  exact Precoverage.generate_mem_toGrothendieck hg

end AlgebraicGeometry
