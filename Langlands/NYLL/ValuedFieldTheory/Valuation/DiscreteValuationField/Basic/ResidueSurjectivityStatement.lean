/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 202, 13 November 2026: extract the listed theorem types
from upstream fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and package each complete source telescope as a Prop-valued
definition. Proofs and theorem attributes are omitted; imports are reduced
to the dependencies of the statements. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF

/-- Statement target for source unit M103.019. -/
def residue_surjectiveStatement.{u, v} : Prop :=
  ∀ {K : Type u} [Field K]
(F : DVF.{u, v} K),
    Function.Surjective F.residueMap

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF
