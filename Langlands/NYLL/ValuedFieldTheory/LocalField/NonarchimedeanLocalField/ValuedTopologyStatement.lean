/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 315 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
the theorem signature is packaged as a Prop-valued definition in Langlands.NYLL;
the proof is omitted. The original license and notice are retained in
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# The topology of the induced valuative relation: statement

This target preserves the topology supplied by `Valued F Γ`.
The only locally introduced instance is the induced `ValuativeRel F`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The supplied topology of a nontrivially valued field is valuative for the
relation induced by its distinguished valuation. -/
def ValuedTopologyStatement : Prop :=
  ∀ (F : Type u) (Γ : Type v)
    [Field F] [LinearOrderedCommGroupWithZero Γ]
    [MulArchimedean Γ] [Valued F Γ]
    [Valuation.IsNontrivial (Valued.v : Valuation F Γ)],
    letI := ValuativeRel.ofValuation (Valued.v : Valuation F Γ)
    IsValuativeTopology F

end Langlands.NYLL.LocalFieldTheory
