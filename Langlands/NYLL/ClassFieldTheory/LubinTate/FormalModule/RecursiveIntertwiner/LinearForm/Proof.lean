/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 463 on 2026-11-15: extracted only the theorem M353.001
(lines 40–44) of Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709; prefixed the namespace
with Langlands.NYLL; imported the published Statement module instead of the
source imports; stated the conclusion as the published proposition
linearForm_hasLinearTermStatement L; opened the proof with `unfold` before the
unchanged source tactic; omitted the unused section variable pi, the source
overview and all other declarations; added a module description.
Details are in the paired Markdown; LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.LinearForm.Statement

/-!
# The prescribed linear form has its own linear term (NYLL M353.001)

For a local field `F` and a finite variable type `sigma`, the multivariable
linear form `∑ i, C (L i) * X i` over the valuation subring of `F` has the
prescribed linear term `L`: its difference from itself is zero, whose order is
`⊤ ≥ 2`.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

/-- The prescribed linear form itself has the prescribed linear term. -/
theorem linearForm_hasLinearTerm
    (L : sigma → F.valuationSubring) :
    linearForm_hasLinearTermStatement L := by
  unfold linearForm_hasLinearTermStatement
  simp [HasLinearTerm]

end Langlands.NYLL.LubinTate.SameUniformizer

end
