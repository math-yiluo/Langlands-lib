/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 643: extract M144.069 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace, imports and target type.
The unavailable M132.017 prerequisite is proved locally under a private name,
using the source's maximal-ideal neighborhood argument (M132.012/.013/.016/.017).
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U063.U063.Proofs

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory Filter
open scoped ValuativeRel

universe u

private theorem signedPowersTendstoZeroForNormalBasis
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x : 𝒪[F]}
    (hx : x ∈ (𝓂[F] : Ideal 𝒪[F])) :
    Tendsto (fun d : Nat => (-x) ^ (d + 1)) atTop (nhds (0 : 𝒪[F])) := by
  rw [tendsto_def]
  intro s hs
  rcases (mem_nhds_subtype ((ValuativeRel.valuation F).integer : Set F)
      (0 : 𝒪[F]) s).1 hs with ⟨t, ht, hts⟩
  rcases (IsValuativeTopology.hasBasis_nhds_zero F).mem_iff.mp ht with
    ⟨γ, -, hγt⟩
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[F] with ⟨ϖ, hϖ⟩
  rcases exists_pow_lt₀
      (Valuation.integer.v_irreducible_lt_one (v := ValuativeRel.valuation F) hϖ)
      γ with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with d hd
  apply hts
  apply hγt
  have hmem : (-x) ^ (d + 1) ∈ (𝓂[F] ^ N : Ideal 𝒪[F]) :=
    Ideal.pow_le_pow_right (le_trans hd (Nat.le_succ d))
      (Ideal.pow_mem_pow ((𝓂[F] : Ideal 𝒪[F]).neg_mem hx) (d + 1))
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation F) hϖ N
  change (-x) ^ (d + 1) ∈ ((𝓂[F] ^ N : Ideal 𝒪[F]) : Set 𝒪[F]) at hmem
  rw [hset] at hmem
  exact hmem.trans_lt hN

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- Successive signed powers of the deviation from one tend to zero. -/
theorem chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zeroStatement K L hle hu := by
  have hu_one := chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one K L hle hu
  change ((u : 𝒪[L]) - 1) ∈ (𝓂[L] ^ 1 : Ideal 𝒪[L]) at hu_one
  have hmax : ((u : 𝒪[L]) - 1) ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    simpa only [pow_one] using hu_one
  exact signedPowersTendstoZeroForNormalBasis L hmax

end Langlands.NYLL.CyclicCohomology
