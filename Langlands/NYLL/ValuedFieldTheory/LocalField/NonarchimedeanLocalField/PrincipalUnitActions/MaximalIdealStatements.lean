/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 202, 13 November 2026: extract the listed theorem types
from upstream fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and package each complete source telescope as a Prop-valued
definition. Proofs and theorem attributes are omitted; imports are reduced
to the dependencies of the statements. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.RingTheory.Ideal.Operations

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

/-- Statement target for source unit M135.001. -/
def integerRingEquiv_mem_maximalIdealStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (x : 𝒪[K]),
    e x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K])

/-- Statement target for source unit M135.002. -/
def integerRingEquiv_map_maximalIdealStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]),
    Ideal.map e.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K])

/-- Statement target for source unit M135.003. -/
def integerRingEquiv_map_maximalIdeal_powStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat),
    Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) =
      (𝓂[K] ^ n : Ideal 𝒪[K])

/-- Statement target for source unit M135.004. -/
def integerRingEquiv_mem_maximalIdeal_powStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat) (x : 𝒪[K]),
    e x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] ^ n : Ideal 𝒪[K])

end Langlands.NYLL.LocalFieldTheory
