/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 168: extracted M001.001 as a Prop-valued statement target,
added the Langlands.NYLL namespace, and reduced imports to KrullTopology.
The source proof and subsequent separable-closure constructions are omitted.
-/

import Mathlib.FieldTheory.KrullTopology

/-!
# Continuity of automorphism conjugation in the Krull topology

Statement extracted from `AlgebraicNumberTheory.continuous_algEquiv_autCongr`
in the pinned NYLL source, SeparableClosureEmbedding.lean, lines 28–57 (the inventory/task locator says 28–54).
-/

namespace Langlands.NYLL.AlgebraicNumberTheory

/-- Conjugation by an algebra equivalence is continuous on automorphism groups
with their canonical Krull topologies. -/
def continuous_algEquiv_autCongrStatement
    {F E E' : Type*}
    [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E']
    (e : E ≃ₐ[F] E') : Prop :=
  Continuous (AlgEquiv.autCongr e)

end Langlands.NYLL.AlgebraicNumberTheory
