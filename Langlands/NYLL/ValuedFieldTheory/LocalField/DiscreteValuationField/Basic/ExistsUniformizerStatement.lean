/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 486, 2026-11-14: extract only the type of M334.008
(lines 73–76) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL, suffix the name with Statement and package the complete
source telescope as a Prop-valued definition. The proof is omitted and
the imports are reduced to the published LocalField definitions module.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions

/-!
# Existence of a uniformizer in a local-field package: statement target

This module states, as a proposition, the theorem `exists_uniformizer` of
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField

/-- Statement target for source unit M334.008: a local-field package has a
uniformizer, an element of its valuation subring that is a uniformizer of
the chosen complete discrete valuation. -/
def exists_uniformizerStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K),
    ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K)

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField
