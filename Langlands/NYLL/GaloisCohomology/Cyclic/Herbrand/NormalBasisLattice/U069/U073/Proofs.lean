/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 643: extract M144.073 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace, imports and exact target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U069.U072.Proofs

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory Filter
open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

theorem chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_oneStatement K L hle hu := by
  have h :=
    chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_inv
      K L hle hu
  simpa [chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_oneStatement,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    h.sub (tendsto_const_nhds (x := (1 : L)))


end Langlands.NYLL.CyclicCohomology
