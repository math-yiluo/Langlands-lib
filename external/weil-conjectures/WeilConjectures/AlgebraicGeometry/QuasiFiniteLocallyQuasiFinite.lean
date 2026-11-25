/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Quasi-finite morphisms are locally quasi-finite and quasi-compact

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/
lemma-nagata-zmt-open-immersion-affine-factorization/pqf-lem-qf-locqf-qc.md, node
pqf-lem-qf-locqf-qc, order 200 (blueprint: pqf-lem-qf-locqf-qc).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism is quasi-finite exactly when it is locally quasi-finite and
quasi-compact, in the sense of Stacks Tag 01TD.

Source: Stacks Project, Morphisms of Schemes, Tag 01TJ
(blueprint: pqf-lem-qf-locqf-qc).

Proof:
1. Suppose `f` is quasi-finite. By `pqf-def-quasifinite` and
   `definition-ind-etale-pro-etale-weakly--3`, it is locally of finite type and
   quasi-compact, and every point is isolated in its fibre. Choose affine
   neighbourhoods of a source point and its image. Apply
   `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` to obtain
   the finite-type affine quasi-finite-at-prime condition. This gives
   quasi-finiteness at every point, hence local quasi-finiteness.
2. Conversely, `lem-weil-pbc-lqf-locally-finite-type` gives local finite
   type from local quasi-finiteness. Together with quasi-compactness this
   gives finite type by `definition-ind-etale-pro-etale-weakly--3`. Apply
   `lem-weil-pbc-quasi-finite-at-point-isolated` at each point to obtain
   isolated fibre points. The definition `pqf-def-quasifinite` now gives
   quasi-finiteness.
-/
theorem isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact
    {X S : AlgebraicGeometry.Scheme.{v}} (f : X ⟶ S) :
    IsQuasiFinite f ↔ IsLocallyQuasiFinite f ∧ AlgebraicGeometry.QuasiCompact f := by
  constructor
  · rintro ⟨hlft, hqc, hisolated⟩
    let := hlft
    refine ⟨?_, hqc⟩
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
    refine ⟨U, hxU, hU, V, hV, hUV, ?_⟩
    exact f.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber x (hisolated x)
      U V hU hV hxU hUV
  · rintro ⟨hlqf, hqc⟩
    have hlft := locallyOfFiniteType_of_isLocallyQuasiFinite f hlqf
    let := hlft
    refine ⟨hlft, hqc, ?_⟩
    intro x
    exact (quasiFiniteAtPoint_isolated_in_fiber f x (hlqf x)).1

end AlgebraicGeometry.Scheme.Hom
