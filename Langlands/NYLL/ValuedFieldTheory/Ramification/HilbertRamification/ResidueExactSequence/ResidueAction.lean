/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 215, 2026-11-14: adaptation of NYLL M243.023–.024 for
Task 5836 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Namespace prefixed with Langlands.NYLL; selected source rows extracted
into a focused module with published Library imports.
See the paired Markdown for the source lines and all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.IsInvariantProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.StabilizerEqTopProof

namespace Langlands.NYLL.RamificationTheory

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- The canonical identification of the decomposition group with the
stabilizer of the selected maximal ideal. -/
def decompositionGroupToMaximalIdealStabilizer
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) where
  toFun sigma := ⟨sigma, by
    rw [decompositionGroup_maximalIdeal_stabilizer_eq_top (K := K) A]
    exact Subgroup.mem_top sigma⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The residue-action exact sequence: the residue action of `G_w` on `λ/κ`. -/
def decompositionGroupResidueAction
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (Ideal.Quotient.stabilizerHom
      (IsLocalRing.maximalIdeal A)
      (decompositionFixedMaximalIdeal K A)
      (decompositionGroup K A)).comp
    (decompositionGroupToMaximalIdealStabilizer (K := K) A)


end ValuationSubring
end HilbertRamification

end
end Langlands.NYLL.RamificationTheory
