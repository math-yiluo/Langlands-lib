/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.Definitions

/-!
# NYLL closed cyclic subgroup conjugation target

Modified by Worker 196, 13 November 2026: extract M052.002, lines 114–119 (proof omitted, lines 120–133) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/TransferOrbitClosure.lean` at `fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with
`Langlands.NYLL`, use focused imports and turn source theorems into Prop-valued
definitions without their proofs. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

def mem_closedSubgroupGenerated_conjugate_iffStatement
    {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (q x c : Q) : Prop :=
    c ∈ (closedSubgroupGenerated ({x} : Set Q)).toSubgroup ↔
      q * c * q⁻¹ ∈
        (closedSubgroupGenerated ({q * x * q⁻¹} : Set Q)).toSubgroup

end
end Langlands.NYLL.ClassFormation
