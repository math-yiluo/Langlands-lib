/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 215, 2026-11-14: adaptation of NYLL M243.018 for
Task 5836 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Namespace prefixed with Langlands.NYLL; selected source rows extracted
into a focused module with published Library imports.
See the paired Markdown for the source lines and all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.MaximalIdealProof

namespace Langlands.NYLL.RamificationTheory

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- Canonical identification of the literal residue field of `Z_w` with the
base residue field used by the residue-action exact sequence. -/
def decompositionFieldResidueEquiv
    (A : _root_.ValuationSubring L) :
    IsLocalRing.ResidueField (decompositionFieldValuationSubring K A) ≃+*
      decompositionResidueField K A :=
  (IsLocalRing.ResidueField.mapEquiv
      (decompositionFieldValuationSubringEquivFixedSubring (K := K) A)).trans
    (Ideal.quotientEquivAlgOfEq ℤ
      (decompositionFixedMaximalIdeal_eq_maximalIdeal (K := K) A).symm).toRingEquiv


end ValuationSubring
end HilbertRamification

end
end Langlands.NYLL.RamificationTheory
