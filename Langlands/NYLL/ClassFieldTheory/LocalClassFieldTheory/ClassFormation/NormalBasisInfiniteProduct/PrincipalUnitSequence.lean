/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M150.007 from NYLL fbd320cd,
-- prefix the namespace and narrow imports. See PrincipalUnitSequence.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.U002.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

def chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (i : Nat) : principalUnits L (1 + i) :=
  ⟨z i,
    chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
      (K := K) (L := L) hb hbn (hz i)⟩

end

end Langlands.NYLL.LocalClassFieldTheory
