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

/-- The cardinality of the finite level-`k` parameter subgroup in the
principal-unit range. -/
def standardLubinTateUnitParameterSubgroup_natCardStatement
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (_hk : 1 ≤ k) (_hkn : k ≤ n + 1) : Prop :=
  Nat.card (standardLubinTateUnitParameterSubgroup F n k) =
    Nat.card F.residueField ^ (n + 1 - k)

end Langlands.NYLL.LubinTate
