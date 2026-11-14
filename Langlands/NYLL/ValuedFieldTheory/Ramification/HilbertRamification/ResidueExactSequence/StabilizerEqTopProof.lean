/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 173, 2026-11-14: proof of NYLL M243.022
`decompositionGroup_maximalIdeal_stabilizer_eq_top` (lines 250–272 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709). The namespace is
prefixed with Langlands.NYLL; the theorem's type is the published closed target
`decompositionGroup_maximalIdeal_stabilizer_eq_topStatement`, and the source tactic
proof is kept unchanged after an `intro` of the closed telescope. The paired
Markdown records all modifications.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements

/-!
# The decomposition group stabilizes the maximal ideal

NYLL M243.022: every element of the decomposition group `G_w` of a valuation subring
`A` maps the maximal ideal of `A` onto itself, so the stabilizer of that ideal in
`G_w` is the whole group.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise

/-- Every decomposition-group automorphism stabilizes the maximal ideal of
the selected valuation ring. -/
theorem decompositionGroup_maximalIdeal_stabilizer_eq_top :
    decompositionGroup_maximalIdeal_stabilizer_eq_topStatement.{u, v} := by
  intro K L _ _ _ A
  apply top_unique
  intro sigma _hsigma
  change sigma • IsLocalRing.maximalIdeal A = IsLocalRing.maximalIdeal A
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma⁻¹)
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma)

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
