/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 768, 2026-11-16: extract the proof of M334.008 from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify the
namespace with Langlands.NYLL, give the theorem the published closed
statement as its type and introduce its telescope in the proof. Replace
the source imports by the published statement and CompleteDVF uniformizer
proof modules; retain the source proof term and declaration docstring.
Omit the other declarations and unused universes w and x, and replace
the module documentation. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ExistsUniformizerStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U022.Proofs

/-!
# A local-field package has a uniformizer

This module proves the published target for NYLL source unit M334.008
using the published proof of M107.022, as in the original source.
-/

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField

universe u v

/-- A local field package has a uniformizer. -/
theorem exists_uniformizer : exists_uniformizerStatement.{u, v} := by
  intro K _ F
  exact F.toCompleteDVF.exists_uniformizer

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField
