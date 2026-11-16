/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.CompositumFixedField.Statements

/-!
# The fixed field of an abstract compositum

Modified by Worker 667, 16 November 2026: extract the proof of M300.005
(lines 128–144) of NYLL's
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace
with `Langlands.NYLL`, replace the broad source imports by the published
statement module, omit unused namespace openings, and state the theorem
against its published proposition target. Unfolding that target exposes the
unchanged source equality proof. The complete source telescope is retained.
See the paired Markdown for the proof and modification record, and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for the retained license
and notices.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

/-- The concrete fixed field of an abstract compositum is the compositum of
the two concrete fixed fields inside the chosen separable closure. -/
theorem finiteAbelianSubextension_compositum_fixedField
    (K : Type) [Field K]
    (U T : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianSubextension_compositum_fixedFieldStatement K U T := by
  unfold finiteAbelianSubextension_compositum_fixedFieldStatement
  let EU := abstractFixedField K (SeparableClosure K) U.field
  let ET := abstractFixedField K (SeparableClosure K) T.field
  rw [← InfiniteGalois.fixedField_fixingSubgroup (EU ⊔ ET)]
  apply congrArg IntermediateField.fixedField
  change
    (U.field.toSubgroup ⊓ T.field.toSubgroup) =
      (EU ⊔ ET).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_sup]
  rw [show EU.fixingSubgroup = U.field.toSubgroup by
      exact InfiniteGalois.fixingSubgroup_fixedField U.field,
    show ET.fixingSubgroup = T.field.toSubgroup by
      exact InfiniteGalois.fixingSubgroup_fixedField T.field]

end Langlands.NYLL.LocalClassFieldTheory
