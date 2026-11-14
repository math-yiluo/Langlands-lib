/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 409, 2026-11-14: extract only the statements of
M335.002–004 (lines 49–72) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, replace each theorem by a Prop-valued definition of its
statement with the suffix Statement, omit the proofs and the simp
attributes, import only the M335.001 definition module, and replace the
module documentation. See the paired Markdown for the complete record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Definitions

/-!
# Comparison targets for the canonical local-field package

Proposition targets stating that the package `standardLocalField K`
forgets to the canonical complete discrete valuation, carries the valuation
of the given valuative relation, and has a residue field of the same
cardinality as `𝓀[K]`.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Forgetting residue-field finiteness recovers the canonical complete-DVF
package used by finite local reciprocity. -/
def standardLocalField_toCompleteDVFStatement : Prop :=
  (standardLocalField K).toCompleteDVF =
    LocalFieldTheory.localCompleteDVF K

/-- The valuation in the canonical local-field package is the valuation
attached to the given valuative relation. -/
def standardLocalField_valuation_eqStatement : Prop :=
  (standardLocalField K).valuation =
    ValuativeRel.valuation K

/-- The residue field in the canonical package has the same finite
cardinality as the topology-first residue field. -/
def standardLocalField_residueField_natCardStatement : Prop :=
  Nat.card (standardLocalField K).residueField =
    Nat.card 𝓀[K]

end Langlands.NYLL.LubinTate
