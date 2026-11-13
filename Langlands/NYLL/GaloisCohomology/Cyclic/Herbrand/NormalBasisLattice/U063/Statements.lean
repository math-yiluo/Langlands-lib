/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 232 from the NYLL pinned source units listed in the paired Markdown.
The namespace and imports are adapted. Source data bodies are unchanged;
source theorems are replaced by exact Prop-valued definitions.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

def chosenNormalBasisPrincipalUnitSet_mem_principalUnits_oneStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    u ∈ principalUnits L 1

def exists_chosenNormalBasisPrincipalUnitSet_mul_closed_le_principalUnits_oneStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      (∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
          u * v ∈ chosenNormalBasisPrincipalUnitSet K L n) ∧
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u ∈ principalUnits L 1

end

end Langlands.NYLL.CyclicCohomology
