/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 643: extract M144.072 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace, imports and exact target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.U071.Proofs

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory Filter
open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- Finite inverse approximations tend to the inverse unit. -/
theorem chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_inv
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_invStatement K L hle hu := by
  have hprod :=
    chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_one
      K L hle hu
  have hmul :
      Tendsto
        (fun d : Nat =>
          (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
            ((((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
              (1 + inverseCorrectionPartialSum (L := L)
                ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)))
        atTop (nhds ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))) := by
    simpa using
      (tendsto_const_nhds (x := (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))).mul hprod
  refine hmul.congr' (Eventually.of_forall ?_)
  intro d
  have huinv :
      ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L)) *
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) : L)) = 1 := by
    have huinvₒ :
        (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) * ((u : 𝒪[L]ˣ) : 𝒪[L])) = 1 :=
      Units.inv_mul u
    exact congrArg (algebraMap 𝒪[L] L) huinvₒ
  rw [← mul_assoc, huinv, one_mul]


end Langlands.NYLL.CyclicCohomology
