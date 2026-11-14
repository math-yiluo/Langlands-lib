/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.OrderStatements

/-!
# NYLL M296.018: the left subextension lies below its compositum

Modified by Worker 275, 14 November 2026: extract M296.018, source lines
251–257 of `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace
with `Langlands.NYLL`, import the published target and its data, and express
the conclusion as that target applied to the same source arguments. The
proof is unchanged except for layout. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The left subextension embeds into the compositum. -/
theorem le_compositum_left (L₁ L₂ : FiniteAbelianSubextension K) :
    le_compositum_leftStatement L₁ L₂ := by
  change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
    L₁.field.toSubgroup
  exact inf_le_left

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
