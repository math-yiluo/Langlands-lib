/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 238, 2026-11-16: extract only M335.004 (lines 66–72)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL, use the published proposition target
as the theorem's type, replace the source imports by the focused Statements
module, omit unused opens, and replace the module documentation. Retain
the source telescope, docstring, simp attribute and rfl proof.
See the paired Markdown and the retained licenses/NYLL/LICENSE and NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Statements

/-!
# Residue cardinality of the canonical local-field package

The residue field of `standardLocalField K` is definitionally the
topology-first residue field, so their natural cardinalities agree.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The residue field in the canonical package has the same finite
cardinality as the topology-first residue field. -/
@[simp]
theorem standardLocalField_residueField_natCard :
    standardLocalField_residueField_natCardStatement K :=
  rfl

end Langlands.NYLL.LubinTate
