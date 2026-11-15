/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 4699, 2026-11-15: prove the published closed target of M138.028,
the theorem maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank at lines 356–380 of
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, under the same name prefixed
with Langlands.NYLL. The theorem's type is the published closed proposition, so the
source binders become an opening intro; the source proof (lines 367–380) is otherwise
unchanged. The source imports are replaced by the published statement module and two
Mathlib modules. The retained license and notices are in licenses/NYLL/.
-/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationInertiaDegreeStatement

/-!
# Ramification index times inertia degree: proof

This module proves the published closed target for NYLL M138.028.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The actual ramification index and inertia degree of the valuation-integer
ring extension satisfy the local ramification identity. This proves the closed
target for NYLL M138.028. -/
theorem maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank :
    maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrankStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  classical
  have := FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L
  have hp := IsDiscreteValuationRing.not_a_field 𝒪[K]
  have hprimes := IsLocalRing.primesOver_eq (A := 𝒪[L]) hp
  have hq (q : (𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :
      (q : Ideal 𝒪[L]) = 𝓂[L] :=
    Set.mem_singleton_iff.mp (hprimes ▸ q.property)
  let : Unique ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :=
    { default := ⟨𝓂[L], hprimes ▸ Set.mem_singleton _⟩
      uniq := fun q => Subtype.ext (Set.mem_singleton_iff.mp (hprimes ▸ q.property)) }
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L]
  simpa only [Fintype.sum_unique, hq] using
    (Ideal.sum_ramification_inertia_eq_finrank (𝓂[K] : Ideal 𝒪[K]) 𝒪[L])

end Langlands.NYLL.LocalFieldTheory
