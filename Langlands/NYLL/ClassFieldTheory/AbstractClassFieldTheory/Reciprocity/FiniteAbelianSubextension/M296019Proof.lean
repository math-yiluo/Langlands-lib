/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.OrderStatements

/-!
# NYLL M296.019: the right subextension lies below its compositum

Modified by Worker 662, 14 November 2026: extract M296.019 (source
lines 259–265) from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, and import the published target and its data by module name.
The conclusion is written as the published `le_compositum_rightStatement`
applied to the same arguments. The source telescope and proof are preserved.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The right subextension embeds into the compositum. -/
theorem le_compositum_right (L₁ L₂ : FiniteAbelianSubextension K) :
    le_compositum_rightStatement L₁ L₂ := by
  change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
    L₂.field.toSubgroup
  exact inf_le_right

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
