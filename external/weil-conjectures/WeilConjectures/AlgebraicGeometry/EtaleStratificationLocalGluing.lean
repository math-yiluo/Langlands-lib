/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore

/-!
# Gluing finite étale constructible stratifications

Source: Stacks Project, Etale Cohomology, `lemma-etale-stratified-finite`, the reduction
"In general, we may assume X is affine"
(blueprint: lem-weil-pbc-etale-stratification-local-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Constructible locally closed partitions with finite étale pullbacks glue over a finite
 affine open cover of a qcqs scheme. Source: Stacks Project, Etale Cohomology,
`lemma-etale-stratified-finite`, locality reduction
(blueprint: lem-weil-pbc-etale-stratification-local-gluing).

Proof:
1. Each affine chart is quasi-compact and retrocompact in the qcqs base
   (`lem-weil-pbc-qcqs-scheme-spectral`,
   `lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`). Its local strata are
   constructible in the base (`lem-weil-pbc-constructible-in-retrocompact-open`).
   Extend the local partition by the closed complement, giving that complement a closed
   subscheme structure (`lem-weil-pbc-closed-subset-closed-subscheme`). Composition of
   immersions makes the local strata locally closed subschemes of the base.
2. Iterate `lemma-constructible-common-refinement` over the finitely many extended
   partitions. Every refined part lies in one local part in some chart, because the
   charts cover the base.
3. For a refined stratum Z contained set-theoretically in a local stratum W, replace its
   scheme representative by Z ×_X W. Its map to X is an immersion with the same image
   (`lem-weil-pbc-immersion-base-change-lft`, `lem-weil-pbc-proper-fp-permanence`,
   `lem-weil-pbc-base-change-image`). Pull back the given finite étale map along the
   projection to W (`lem-weil-pbc-finite-morphism-permanence`,
   `lem-weil-pbc-etale-scheme-base-change`). Fibre-product associativity identifies this
   map with the required pullback of U to the replacement stratum. -/
theorem exists_constructible_stratification_finite_etale_of_affine_local
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ X) [Etale j]
    (hlocal : ∃ (n : ℕ) (W : Fin n → X.Opens),
      (∀ a : Fin n, IsAffineOpen (W a)) ∧
      (⋃ a : Fin n, (W a : Set X)) = Set.univ ∧
      ∀ a : Fin n, ∃ S : Stratification (W a),
        (∀ b : Fin S.n, Topology.IsConstructible (S.stratum b)) ∧
        ∀ b : Fin S.n,
          IsFinite (pullback.snd j (S.immersion b ≫ (W a).ι)) ∧
          Etale (pullback.snd j (S.immersion b ≫ (W a).ι))) :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i)) := by
  classical
  obtain ⟨n, W, hW, hcover, hlocal⟩ := hlocal
  choose T hc hf using hlocal
  obtain ⟨S, hS, hfactor⟩ :=
    exists_global_stratification_factoring_local n W hW hcover T hc
  refine ⟨S, hS, ?_⟩
  intro i
  obtain ⟨a, b, q, hq⟩ := hfactor i
  let g := (T a).immersion b ≫ (W a).ι
  have : IsFinite (pullback.snd j g) := (hf a b).1
  have : Etale (pullback.snd j g) := (hf a b).2
  rw [← hq]
  let e := pullbackLeftPullbackSndIso j g q
  have he : e.inv ≫ pullback.snd (pullback.snd j g) q =
      pullback.snd j (q ≫ g) := pullbackLeftPullbackSndIso_inv_snd_snd j g q
  rw [← he]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
