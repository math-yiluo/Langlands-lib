/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 519: extract M150.003 from NYLL fbd320cd,
-- prove the exact published target, and reproduce the needed zero-neighborhood
-- estimate privately from Mathlib's valuation basis. See Proofs.md and licenses/NYLL/.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.LatticeBoundStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.U002.Proofs
import Mathlib.GroupTheory.ArchimedeanDensely

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section
universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open Filter

private theorem m150_eventual_ideal_powers
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (s : Set 𝒪[F])
    (hs : s ∈ nhds (0 : 𝒪[F])) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m →
      ((𝓂[F] ^ m : Ideal 𝒪[F]) : Set 𝒪[F]) ⊆ s := by
  rcases (mem_nhds_subtype ((ValuativeRel.valuation F).integer : Set F)
      (0 : 𝒪[F]) s).1 hs with ⟨t, ht, hts⟩
  rcases (IsValuativeTopology.hasBasis_nhds_zero F).mem_iff.mp ht with
    ⟨γ, -, hγt⟩
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[F] with ⟨ϖ, hϖ⟩
  rcases exists_pow_lt₀
      (Valuation.integer.v_irreducible_lt_one (v := ValuativeRel.valuation F) hϖ)
      γ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm x hx
  apply hts
  apply hγt
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation F) hϖ N
  have hxset : x ∈ ((𝓂[F] ^ N : Ideal 𝒪[F]) : Set 𝒪[F]) :=
    Ideal.pow_le_pow_right hm hx
  rw [hset] at hxset
  exact hxset.trans_lt hN

theorem tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤ integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_boundStatement
      K L hb hbn z hz := by
  change Tendsto (fun i : Nat => ((z i : 𝒪[L]ˣ) : 𝒪[L])) atTop (nhds (1 : 𝒪[L]))
  have hsub : Tendsto
      (fun i : Nat => ((z i : 𝒪[L]ˣ) : 𝒪[L]) - 1) atTop
      (nhds (0 : 𝒪[L])) := by
    rw [tendsto_def]
    intro s hs
    rcases m150_eventual_ideal_powers L s hs with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with i hi
    apply hN (1 + i)
    · exact le_trans hi (Nat.le_add_left i 1)
    · exact (mem_principalUnits_iff L (z i) (1 + i)).1
        (chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
          K L hb hbn (hz i))
  simpa using hsub.const_add (1 : 𝒪[L])

end
end Langlands.NYLL.LocalClassFieldTheory
