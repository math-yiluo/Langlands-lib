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
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U086.Definitions
import Mathlib.RingTheory.Valuation.Extension

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

def chosenNormalBasisPrincipalUnitLatticeClass (n : Nat)
    (u : 𝒪[L]ˣ) (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisLatticeSuccQuot K L n :=
  chosenNormalBasisLatticeSuccQuotMk K L n
    ⟨((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L), hu⟩

end

end Langlands.NYLL.CyclicCohomology
