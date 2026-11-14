/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 14 November 2026:
Extract the proof of M135.004 (lines 58–75) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitActions.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement by introducing its
telescope. The source rewrites with the M135.003 theorem for e and e.symm,
which rests on M135.001–002; their source proofs are inlined as the local
fact hpow, quantified over the ring equivalence, which replaces both source
rewrites. Import only the target statement module. Omit all other source
declarations. See paired Markdown. The upstream LICENSE and NOTICE are
preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions.MaximalIdealStatements

/-!
# Membership in maximal-ideal powers under valuation-ring equivalences

The exact proof of NYLL M135.004.
-/

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

/-- Membership in every maximal-ideal power is invariant under an integer-ring equivalence. -/
theorem integerRingEquiv_mem_maximalIdeal_pow.{u} :
    integerRingEquiv_mem_maximalIdeal_powStatement.{u} := by
  intro K _ _ e n x
  -- The source proofs of M135.001–003, inlined for an arbitrary ring equivalence.
  have hpow : ∀ f : 𝒪[K] ≃+* 𝒪[K],
      Ideal.map f.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) = (𝓂[K] ^ n : Ideal 𝒪[K]) := by
    intro f
    have hmem : ∀ x : 𝒪[K], f x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K]) := by
      intro x
      rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff f,
        ← IsLocalRing.mem_maximalIdeal]
    have hmap : Ideal.map f.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K]) := by
      ext y
      constructor
      · intro hy
        rcases (Ideal.mem_map_iff_of_surjective f.toRingHom f.surjective).1 hy with
          ⟨x, hx, rfl⟩
        exact (hmem x).2 hx
      · intro hy
        refine (Ideal.mem_map_iff_of_surjective f.toRingHom f.surjective).2 ?_
        refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
        have hy' : f (f.symm y) ∈ (𝓂[K] : Ideal 𝒪[K]) := by
          simpa using hy
        exact (hmem (f.symm y)).1 hy'
    rw [Ideal.map_pow, hmap]
  constructor
  · intro hx
    have hxmap :
        e.symm (e x) ∈ Ideal.map e.symm.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.symm.toRingHom hx
    rw [hpow e.symm] at hxmap
    simpa using hxmap
  · intro hx
    have hxmap : e x ∈ Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) :=
      Ideal.mem_map_of_mem e.toRingHom hx
    rw [hpow e] at hxmap
    exact hxmap

end Langlands.NYLL.LocalFieldTheory
