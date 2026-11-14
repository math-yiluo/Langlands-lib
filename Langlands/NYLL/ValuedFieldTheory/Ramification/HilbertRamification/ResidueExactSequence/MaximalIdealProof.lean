/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 133 (2026-11-14): proof of NYLL M243.017,
`decompositionFixedMaximalIdeal_eq_maximalIdeal`, from
Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean
(lines 208–216) at commit fbd320cd8b1b06487c58227e92eb135794267709.
The namespace is prefixed with Langlands.NYLL. The theorem's type is the
published closed proposition `decompositionFixedMaximalIdeal_eq_maximalIdealStatement`
at universes u v. The source proof term `IsLocalRing.eq_maximalIdeal` of the
maximality instance M243.016 is replaced by the reversed published Library
theorem `FixedPoints.maximalIdeal_subring_eq_comap`; M243.016 is not used.
Imports are the published statement module and the published fixed-subring
locality module. The section variables, noncomputable section and scopes
are omitted. See the paired Markdown for all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.MaximalIdealStatement
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

/-!
# The contracted maximal ideal is the maximal ideal of the fixed subring (NYLL M243.017)

For a valuation subring `A` of `L` and the decomposition group `G_w` of `A`
over `K`, the contraction of the maximal ideal of `A` to the fixed subring
`A^{G_w}` is the maximal ideal of that local ring.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- The contracted ideal used in the intrinsic presentation is the actual
maximal ideal of the valuation ring on `Z_w`. -/
theorem decompositionFixedMaximalIdeal_eq_maximalIdeal :
    decompositionFixedMaximalIdeal_eq_maximalIdealStatement.{u, v} := by
  intro K L _ _ _ _ A
  exact (FixedPoints.maximalIdeal_subring_eq_comap
    (R := A) (M := decompositionGroup K A)).symm

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
