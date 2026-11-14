/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 411, 2026-11-14: extract only M335.005 (lines 74–89)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL, replace the source imports by the published
standardLocalField module, drop the unused opened namespaces, and discharge
both subtype obligations by definitional reduction to
`ValuativeRel.valuation K` instead of rewriting with the M335.003 theorem.
See the paired Markdown. License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Definitions

/-!
# The standard integer-ring equivalence

The identity on underlying elements of `K` identifies the topology-first
integer ring `𝒪[K]` with the valuation subring of the canonical local-field
package `standardLocalField K`. Extracted from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Identity on underlying field elements identifies the topology-first
integer ring with the valuation ring of the canonical package. -/
noncomputable def standardLocalFieldIntegerEquiv :
    𝒪[K] ≃+* (standardLocalField K).valuationSubring where
  toFun x := ⟨x, by
    change ValuativeRel.valuation K (x : K) ≤ 1
    exact x.property⟩
  invFun x := ⟨x, by
    change ValuativeRel.valuation K (x : K) ≤ 1
    exact x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl

end Langlands.NYLL.LubinTate
