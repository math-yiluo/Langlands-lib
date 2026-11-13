/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-13: extracted the proof of M133.005
from IdealQuotients.lean at fbd320cd8b1b06487c58227e92eb135794267709;
added the Langlands.NYLL namespace prefix, imported the published target
interface, and expressed the theorem type as that exact Prop target.
The original proof term is unchanged. LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The chosen integer-ring uniformizer is irreducible. -/
theorem chosenIntegerRingUniformizer_irreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    chosenIntegerRingUniformizer_irreducibleStatement K :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[K])

end Langlands.NYLL.LocalFieldTheory
