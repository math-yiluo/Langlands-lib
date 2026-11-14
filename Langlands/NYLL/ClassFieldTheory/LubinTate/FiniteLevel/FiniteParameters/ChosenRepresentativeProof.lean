/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 439 (2026-11-14): extract the M358.006 proof alone
from the pinned source at fbd320cd8b1b06487c58227e92eb135794267709; prefix
its namespace by Langlands.NYLL, import its published Prop target, and prove
that exact target. Details are recorded in the paired Markdown. Retained
license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.RepresentativeStatements

noncomputable section
universe u v
namespace Langlands.NYLL.LubinTate
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
variable {K : Type u} [Field K]

/-- M358.006: the chosen representative has the prescribed quotient class. -/
@[simp]
theorem standardLubinTateUnitParameterChosenRepresentative_spec
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterChosenRepresentative_specStatement F n a :=
  Classical.choose_spec
    (QuotientGroup.mk'_surjective
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a)

end Langlands.NYLL.LubinTate
end
