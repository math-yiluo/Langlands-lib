/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 643: extract M144.063 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, adapt namespace and imports,
and unfold the maximal-ideal image and principal-unit membership directly.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U063.Statements

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory
open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- A principal unit from the normal-basis lattice lies in the first principal-unit group. -/
theorem chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitSet_mem_principalUnits_oneStatement K L hle hu := by
  change (((u : 𝒪[L]) - 1) ∈ (𝓂[L] ^ 1 : Ideal 𝒪[L]))
  have hmax := hle hu
  rcases hmax with ⟨a, ha, haeq⟩
  have ha_eq : a = (u : 𝒪[L]) - 1 := Subtype.ext haeq
  simpa only [pow_one, ha_eq] using ha

end Langlands.NYLL.CyclicCohomology
