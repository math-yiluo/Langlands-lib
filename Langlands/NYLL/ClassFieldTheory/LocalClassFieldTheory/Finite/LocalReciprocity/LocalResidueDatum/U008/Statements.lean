/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: state only the Prop-valued instance M249.008,
lines 106–109 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the closed
proposition localSeparableValuationHasExtensionStatement in the
Langlands.NYLL.LocalClassFieldTheory namespace; the section variables of the
source become its leading universally quantified binders; the target is an
`abbrev`, so that a proof can be registered as an instance. The source proof
and the instance attribute are not part of this module. The retained license
and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions

/-!
# The chosen separable valuation extends the local valuation: target

This module states only the Prop-valued instance M249.008, lines 106–109 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Closed target for the NYLL M249.008 instance
`localSeparableValuationHasExtension`: the valuation of the chosen valuation
ring of `SeparableClosure K` extends the canonical discrete valuation of the
nonarchimedean local field `K`. -/
abbrev localSeparableValuationHasExtensionStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation.HasExtension
      (localSeparableValuationSubring K).valuation

end Langlands.NYLL.LocalClassFieldTheory
