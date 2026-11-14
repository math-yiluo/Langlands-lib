/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: extract the indicated units from NYLL
at pinned commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the
namespace with Langlands.NYLL and use focused shared-interface imports.
See the paired Markdown for the extraction and target/proof split.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration.Definitions

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- A represented finite parameter belongs to level `k` exactly when its
representative does, provided `k ≤ n + 1`. -/
def standardLubinTateUnitParameterClass_mem_subgroup_iffStatement
    (F : LocalField.{u, v} K) (n k : ℕ) (_hk : k ≤ n + 1)
    (u : F.valuationSubringˣ) : Prop :=
  standardLubinTateUnitParameterClass F n u ∈
      standardLubinTateUnitParameterSubgroup F n k ↔
    u ∈ higherPrincipalUnitGroup F.toCompleteDVF k

end Langlands.NYLL.LubinTate
