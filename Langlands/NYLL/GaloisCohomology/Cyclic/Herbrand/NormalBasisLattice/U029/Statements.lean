/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 231 on 2026-11-13: extracted the listed theorem types
as Prop-valued definitions, removed their proofs, prefixed the namespace
with Langlands.NYLL and reduced imports. See the paired source map.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U030.Definitions

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

set_option linter.unusedVariables false

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
def submodule_pow_succ_mem_of_mul_closedStatement
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) : Prop :=
    ∀ m : Nat, x ^ (m + 1) ∈ E

omit [FiniteDimensional K L] [IsGalois K L] in
def inverseCorrectionPartialSum_succStatement (x : L) (d : Nat) : Prop :=
    inverseCorrectionPartialSum (L := L) x (d + 1) =
      inverseCorrectionPartialSum (L := L) x d + (-x) ^ (d + 1)

omit [FiniteDimensional K L] [IsGalois K L] in
def one_add_inverseCorrectionPartialSum_eq_geom_sumStatement (x : L) (d : Nat) : Prop :=
    1 + inverseCorrectionPartialSum (L := L) x d =
      (Finset.range (d + 1)).sum fun i => (-x) ^ i

omit [FiniteDimensional K L] [IsGalois K L] in
def one_add_mul_one_add_inverseCorrectionPartialSumStatement (x : L) (d : Nat) : Prop :=
    (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) =
      1 - (-x) ^ (d + 1)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
def inverseCorrectionPartialSum_mem_of_mul_closedStatement
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) (d : Nat) : Prop :=
    inverseCorrectionPartialSum (L := L) x d ∈ E

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
def submodule_isOpen_of_mem_nhds_zeroStatement
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : (E : Set L) ∈ nhds (0 : L)) : Prop :=
    IsOpen (E : Set L)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
def submodule_isClosed_of_isOpenStatement
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : IsOpen (E : Set L)) : Prop :=
    IsClosed (E : Set L)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
def submodule_isClosed_of_mem_nhds_zeroStatement
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : (E : Set L) ∈ nhds (0 : L)) : Prop :=
    IsClosed (E : Set L)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
def submodule_mem_of_tendsto_of_forall_mem_of_closedStatement
    [TopologicalSpace L] {E : Submodule 𝒪[K] L} {f : Nat → L} {x : L}
    (hclosed : IsClosed (E : Set L)) (hf : Tendsto f atTop (nhds x))
    (hmem : ∀ d : Nat, f d ∈ E) : Prop :=
    x ∈ E

end
end Langlands.NYLL.CyclicCohomology
