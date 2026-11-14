/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.OrderStatements

/-!
# NYLL M296.020: the compositum lies below any common upper bound

Modified by Worker 663, 14 November 2026: extract only `compositum_le`
(source lines 267–271) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, prefix its namespace
with `Langlands.NYLL`, import the published `OrderStatements` module, and
express its conclusion as `compositum_leStatement h₁ h₂`. The complete
source telescope and proof term are unchanged. Unused source scaffolding is
omitted. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The compositum is the least subextension containing both inputs. -/
theorem compositum_le {L₁ L₂ P : FiniteAbelianSubextension K}
    (h₁ : L₁ ≤ P) (h₂ : L₂ ≤ P) :
    compositum_leStatement h₁ h₂ :=
  fun _ hp => ⟨h₁ hp, h₂ hp⟩

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
