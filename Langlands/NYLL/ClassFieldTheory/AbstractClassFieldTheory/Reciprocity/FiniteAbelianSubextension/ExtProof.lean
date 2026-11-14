/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Statements

/-!
# NYLL M296.013: extensionality of finite abelian subextensions

Modified by Worker 468, 14 November 2026: extract the theorem
`FiniteAbelianSubextension.ext` (M296.013) from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:127–142`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, import the published statement module, and state the result
as the published target `extStatement` applied to the same arguments. Omit
the source `@[ext]` attribute: Lean registers an extensionality theorem only
when its stated type is syntactically an equation, and `extStatement h` is
not. The source proof body is unchanged. Import only the published
statement module; omit the source's other imports, its unused
`open CyclicCohomology KummerTheory` and all other source declarations. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
for attribution and the modification record.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- Two packages with the same closed subgroup represent the same finite
abelian extension. -/
theorem ext {L₁ L₂ : FiniteAbelianSubextension K}
    (h : L₁.field = L₂.field) : extStatement h := by
  cases L₁ with
  | mk L₁ h₁ =>
      cases L₂ with
      | mk L₂ h₂ =>
          cases L₁ with
          | mk F₁ b₁ n₁ f₁ =>
              cases L₂ with
              | mk F₂ b₂ n₂ f₂ =>
                  dsimp only [field] at h
                  cases h
                  rfl

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
