/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 173, 2026-11-14: proof of NYLL M243.016
`decompositionFixedMaximalIdeal.instIsMaximal` (lines 202–206 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709). The namespace is
prefixed with Langlands.NYLL; the source instance becomes a theorem whose type is
the published closed target `decompositionFixedMaximalIdeal.instIsMaximalStatement`,
registered as a global instance by `attribute [instance]`. The source proof through
the private theorem M243.015 `decompositionFixedMaximalIdeal_isMaximal` (lines
179–200) and its profinite-integrality route is replaced by the published Library
theorem `FixedPoints.isMaximal_comap_maximalIdeal_subring`. The paired Markdown
records all modifications.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

/-!
# The contracted maximal ideal of the fixed subring is maximal

NYLL M243.016: for a Galois extension `L / K`, the contraction to the fixed subring
`A^{G_w}` of the maximal ideal of `A` is a maximal ideal. The published Library
theorem `FixedPoints.isMaximal_comap_maximalIdeal_subring` proves this for the fixed
subring of any local commutative ring under any monoid acting by ring automorphisms.
The theorem is registered as a global instance.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- Provides the instance `instIsMaximal`. -/
theorem decompositionFixedMaximalIdeal.instIsMaximal :
    decompositionFixedMaximalIdeal.instIsMaximalStatement.{u, v} := by
  intro K L _ _ _ _ A
  exact FixedPoints.isMaximal_comap_maximalIdeal_subring

attribute [instance] decompositionFixedMaximalIdeal.instIsMaximal

/-- Instance search check: the registered instance applies. -/
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal :=
  inferInstance

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
