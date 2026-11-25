/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of local finite presentation along fpqc coverings

Source: Stacks Project, Descent, Lemma Tag 02KY, descent direction
(blueprint: lem-weil-pbc-fpqc-descend-locally-finite-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Local finite presentation descends along an fpqc covering family of the target.
Source: Stacks Project, Descent, Lemma Tag 02KY
(blueprint: lem-weil-pbc-fpqc-descend-locally-finite-presentation).

Proof:
1. Local finite presentation is invariant under isomorphisms: affine neighbourhoods and
   their finite algebra presentations transport across the isomorphisms. It is Zariski local
   on the target: affine neighbourhoods in open subschemes are affine neighbourhoods in the
   ambient scheme (def-sbc-locally-finite-presentation, def-pc-scheme,
   def-weil-pbc-finitely-presented-algebra).
2. It is stable under base change (lem-weil-pbc-qcqs-morphism-permanence, clause 3; Tag 01TS).
3. For a flat surjective map of affine schemes, write the bases as Spec R and Spec R'.
   The corresponding ring map is flat and surjective on prime spectra, hence faithfully
   flat (lem-weil-pbc-flat-ring-map-iff-flat-affine,
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat).
4. For an affine open Spec A of the source, its inverse image in the base change is affine
   and has ring A tensor R'. Cartesian-square pasting and the affine fibre-product formula
   identify its projection with the base-changed ring map
   (lem-weil-pbc-open-preimage-fibre-product, lem-weil-pbc-cartesian-square-pasting,
   lem-weil-pbc-fibre-product-affine-spectra). Local finite presentation of the base change
   makes this ring map finitely presented (lem-weil-pbc-lfp-affine-opens-finite-presentation).
   Swapping tensor factors makes R' tensor A a finitely presented R'-algebra.
5. Finite presentation descends through the faithfully flat ring map R to R'
   (lem-weil-pbc-finite-presentation-descends-faithfully-flat, Tag 00QQ). Every source point
   lies in an affine open, so the original morphism is locally of finite presentation.
6. These are the isomorphism-invariance, base-change, Zariski-locality and affine-descent
   conditions of the fpqc-local-on-the-base criterion (Tag 02KP). Applying that criterion
   to the given fpqc covering proves the conclusion. -/
theorem locallyOfFinitePresentation_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S)
    {I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, LocallyOfFinitePresentation (pullback.snd f (g i))) :
    LocallyOfFinitePresentation f := by
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology
    (P := @LocallyOfFinitePresentation)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
