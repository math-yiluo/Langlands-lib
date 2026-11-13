/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 215, 2026-11-13: adaptation of M243.017 for Task 5836,
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Namespace prefixed with Langlands.NYLL; the source theorem is replaced
by a closed Prop-valued definition, preserving its elaborated telescope.
Imports use the published NYLL data and fixed-subring locality instance.
The unused section variables, noncomputable section and scopes are omitted.
See the paired Markdown for the source rows and all modifications.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- NYLL M243.017: the contracted ideal is the maximal ideal of the fixed subring. -/
def decompositionFixedMaximalIdeal_eq_maximalIdealStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (A : _root_.ValuationSubring L),
    decompositionFixedMaximalIdeal K A =
      IsLocalRing.maximalIdeal (decompositionFixedSubring K A)

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
