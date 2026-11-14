/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 559 on 14 November 2026 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, StandardOpenSubgroups.lean,
M289.003, lines 43–84. Inline the needed Mathlib argument from
PrincipalUnitQuotients.lean, M132.012, lines 162–188, prefix the namespace,
use focused published imports, and prove the existing fully applied target.
See Proofs.md and licenses/NYLL/ for correspondence and attribution.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Proofs

/-!
# Positive principal-unit groups inside neighborhoods of one
-/

noncomputable section

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel
open Filter

universe u

/-- Every neighborhood of one contains a positive principal-unit group. -/
theorem exists_fieldPrincipalUnits_subset_of_mem_nhds
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (U : Set Kˣ) (hU : U ∈ nhds (1 : Kˣ)) :
    exists_fieldPrincipalUnits_subset_of_mem_nhdsStatement K U hU := by
  obtain ⟨H, hHU, hH, hOneH⟩ := mem_nhds_iff.mp hU
  rcases Units.isEmbedding_val₀.isOpen_iff.mp hH with
    ⟨V : Set K, hVopen, hV⟩
  have hOneV : (1 : K) ∈ V := by
    have hOnePre : (1 : Kˣ) ∈ Units.val ⁻¹' V := hV.symm ▸ hOneH
    exact hOnePre
  let s : Set 𝒪[K] := {a | (((a : 𝒪[K]) : K) + 1) ∈ V}
  have hs : s ∈ nhds (0 : 𝒪[K]) := by
    have hsOpen : IsOpen s := by
      exact hVopen.preimage (continuous_subtype_val.add continuous_const)
    apply hsOpen.mem_nhds
    change ((0 : K) + 1) ∈ V
    rw [zero_add]
    exact hOneV
  have hPower : ∃ N : Nat, ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s := by
    rcases (mem_nhds_subtype ((ValuativeRel.valuation K).integer : Set K)
        (0 : 𝒪[K]) s).1 hs with ⟨t, ht, hts⟩
    rcases (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp ht with
      ⟨γ, -, hγt⟩
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
    rcases exists_pow_lt₀
        (Valuation.integer.v_irreducible_lt_one (v := ValuativeRel.valuation K) hϖ)
        γ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro x hx
    apply hts
    apply hγt
    have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
      (v := ValuativeRel.valuation K) hϖ N
    have hxset : x ∈ ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) := hx
    rw [hset] at hxset
    exact hxset.trans_lt hN
  obtain ⟨N, hN⟩ := hPower
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  have haPowSucc :
      (((a : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
        (𝓂[K] ^ (N + 1) : Ideal 𝒪[K]) :=
    (mem_principalUnits_iff K a (N + 1)).1 ha
  have haPow :
      (((a : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
        (𝓂[K] ^ N : Ideal 𝒪[K]) :=
    Ideal.pow_le_pow_right (Nat.le_succ N) haPowSucc
  have haV : (((a : 𝒪[K]ˣ) : 𝒪[K]) : K) ∈ V := by
    have has := hN haPow
    change (((((a : 𝒪[K]ˣ) : 𝒪[K]) - 1 : 𝒪[K]) : K) + 1) ∈ V at has
    change (((a : 𝒪[K]ˣ) : 𝒪[K]) : K) - 1 + 1 ∈ V at has
    rw [sub_add_cancel] at has
    exact has
  have haPre : Units.map (algebraMap 𝒪[K] K).toMonoidHom a ∈ Units.val ⁻¹' V := haV
  have haH : Units.map (algebraMap 𝒪[K] K).toMonoidHom a ∈ (H : Set Kˣ) := by
    rw [← hV]
    exact haPre
  exact hHU haH

end Langlands.NYLL.LocalFieldTheory
