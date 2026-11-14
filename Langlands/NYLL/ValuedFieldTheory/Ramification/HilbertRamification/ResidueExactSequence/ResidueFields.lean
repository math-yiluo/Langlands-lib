/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 215, 2026-11-14: adaptation of NYLL M243.020–.021 for
Task 5836 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Namespace prefixed with Langlands.NYLL; selected source rows extracted
into a focused module with published Library imports.
See the paired Markdown for the source lines and all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.IsMaximalProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.LiesOverProof

namespace Langlands.NYLL.RamificationTheory

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- Provides the instance `instField`. -/
noncomputable instance decompositionResidueField.instField
    (A : _root_.ValuationSubring L) :
    Field (decompositionResidueField K A) :=
  Ideal.Quotient.field (decompositionFixedMaximalIdeal K A)

/-- Provides the instance `instAlgebra`. -/
noncomputable instance selectedResidueField.instAlgebra
    (A : _root_.ValuationSubring L) :
    Algebra (decompositionResidueField K A) (selectedResidueField A) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (le_of_eq ((IsLocalRing.maximalIdeal A).over_def
      (decompositionFixedMaximalIdeal K A)))


end ValuationSubring
end HilbertRamification

end
end Langlands.NYLL.RamificationTheory
