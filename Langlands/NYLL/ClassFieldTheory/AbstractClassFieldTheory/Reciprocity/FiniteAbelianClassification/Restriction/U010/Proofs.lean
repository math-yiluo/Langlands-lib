/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.Restriction.Statements

/-!
# NYLL M298.010: restriction on quotient representatives

Modified by Worker 783, 16 November 2026: extract M298.010 (lines 248–259)
from the pinned NYLL `FiniteAbelianClassification.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with
`Langlands.NYLL`, import the published target, and state the conclusion as
`restriction_mkStatement h₁₂ k`. Restore the two published local instances
within their source namespace. After the source simplification, close the
remaining raw representative identity by reflexivity. The paired Markdown
describes the adaptation.
See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

namespace FiniteAbelianSubextension

attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
  Langlands.NYLL.PortInternal.M298.d002

/-- Restriction sends the quotient class of a base-subgroup element to its
class in the smaller extension's quotient. -/
@[simp]
theorem restriction_mk
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (k : K.toSubgroup) : restriction_mkStatement h₁₂ k := by
  unfold restriction_mkStatement
  apply L₁.extensionQuotientMulEquiv.injective
  simp [restriction]
  rfl

end FiniteAbelianSubextension

end Langlands.NYLL.ClassFormation
