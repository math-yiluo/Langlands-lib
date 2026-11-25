/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SeparatedOpenInduction
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenIntersectionProperty

/-!
# Induction principle for quasi-compact opens

Source: literature/stacks-project/coherent.tex, Cohomology of Schemes, Lemma 08DR
(coherent-lemma-induction-principle) (blueprint: lem-sc-invert-s-cohomology-induction).
-/

@[expose] public section

universe u

open TopologicalSpace

namespace AlgebraicGeometry

/-- Stacks Project, Cohomology of Schemes, Lemma 08DR: induction for quasi-compact opens
(blueprint: lem-sc-invert-s-cohomology-induction).

First handle separated quasi-compact opens using finite affine covers
(`lem-weil-pbc-qcqs-finite-affine-open-cover`). Induct on their size. The empty
open is affine. Adjoin the last affine V to the union U of the preceding charts.
Each chart's intersection with V is affine by
`lem-weil-pbc-separated-affine-open-intersection`. Thus both U and U ∩ V have
shorter covers and satisfy P by induction. Their separatedness follows from open
immersions and composition (`lem-weil-pbc-separated-cancellation` and
`lem-weil-pbc-proper-fp-permanence`). Apply the gluing hypothesis.

For any quasi-compact open W, induct on a finite affine cover in the same way.
Quasi-separatedness makes U ∩ V quasi-compact
(`lem-weil-pbc-quasi-separated-affine-cover-criterion`). It is separated as an
open of affine V (`lem-sc-separated-over-affine-scheme-separated` and
`lem-weil-pbc-separated-cancellation`). Apply
`lem-sc-invert-s-cohomology-separated-induction` to it, the induction hypothesis
to U, and the affine hypothesis to V, then glue. Finally take W = X. -/
theorem quasiCompactOpen_induction (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (P : X.Opens → Prop)
    (h_affine : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_union : ∀ (U V : X.Opens), IsCompact (U : Set X) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V)) :
    ∀ U : X.Opens, IsCompact (U : Set X) → P U := by
  intro U hU
  refine compact_open_induction_on U hU ?_ ?_
  · exact h_affine _ (isAffineOpen_bot X)
  · exact fun S hS V hPS ↦ h_union S (V : X.Opens) hS V.property hPS
      (h_affine _ V.property)
      (property_intersection_of_quasiCompact_affine X P h_affine h_union S
        (V : X.Opens) hS V.property)

end AlgebraicGeometry
