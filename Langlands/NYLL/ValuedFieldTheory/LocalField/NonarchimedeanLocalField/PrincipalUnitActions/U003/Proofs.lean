/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 14 November 2026:
Extract the proof of M135.003 (lines 50–57) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitActions.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement by introducing its
telescope. The source rewrites with the M135.002 theorem, which rests on
M135.001; their source proofs are inlined as the local facts hmem and hmap,
and hmap replaces the source rewrite lemma. Import only the target statement
module. Omit all other source declarations. See paired Markdown. The
upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements

/-!
# Valuation-ring equivalences map maximal-ideal powers to themselves

The exact proof of NYLL M135.003.
-/

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

/-- A ring equivalence of a valuation integer ring maps every maximal-ideal power to itself. -/
theorem integerRingEquiv_map_maximalIdeal_pow.{u} :
    integerRingEquiv_map_maximalIdeal_powStatement.{u} := by
  intro K _ _ e n
  -- The source proof of M135.001 for `e`, inlined.
  have hmem : ∀ x : 𝒪[K], e x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
      ← IsLocalRing.mem_maximalIdeal]
  -- The source proof of M135.002 for `e`, inlined.
  have hmap : Ideal.map e.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K]) := by
    ext y
    constructor
    · intro hy
      rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hy with
        ⟨x, hx, rfl⟩
      exact (hmem x).2 hx
    · intro hy
      refine (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).2 ?_
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have hy' : e (e.symm y) ∈ (𝓂[K] : Ideal 𝒪[K]) := by
        simpa using hy
      exact (hmem (e.symm y)).1 hy'
  rw [Ideal.map_pow, hmap]

end Langlands.NYLL.LocalFieldTheory
