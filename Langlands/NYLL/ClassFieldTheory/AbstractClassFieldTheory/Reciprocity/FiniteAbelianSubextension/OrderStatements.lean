/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Compositum

/-!
# NYLL M296.015 and M296.018–.020: order and compositum targets

Modified by Worker 448, 14 November 2026: extract the asserted types of the
source theorems M296.015 (`le_iff`, lines 157–160) and M296.018–.020
(`le_compositum_left`, `le_compositum_right`, `compositum_le`, lines 251–271)
of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709` as Prop-valued definitions
without their proofs. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to each theorem name, and import the order (M296.014) and
compositum (M296.017) modules. The paired Markdown records every
modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- Target of `FiniteAbelianSubextension.le_iff`: the order on finite abelian
subextensions is characterized by containment of their fields. -/
def le_iffStatement (L₁ L₂ : FiniteAbelianSubextension K) : Prop :=
    L₁ ≤ L₂ ↔ L₂.field.toSubgroup ≤ L₁.field.toSubgroup

/-- Target of `FiniteAbelianSubextension.le_compositum_left`: the left
subextension embeds into the compositum. -/
def le_compositum_leftStatement (L₁ L₂ : FiniteAbelianSubextension K) : Prop :=
    L₁ ≤ L₁.compositum L₂

/-- Target of `FiniteAbelianSubextension.le_compositum_right`: the right
subextension embeds into the compositum. -/
def le_compositum_rightStatement (L₁ L₂ : FiniteAbelianSubextension K) : Prop :=
    L₂ ≤ L₁.compositum L₂

-- Preserve the source hypotheses even though the conclusion does not mention
-- them.
set_option linter.unusedVariables false in
/-- Target of `FiniteAbelianSubextension.compositum_le`: the compositum is the
least subextension containing both inputs. -/
def compositum_leStatement {L₁ L₂ P : FiniteAbelianSubextension K}
    (h₁ : L₁ ≤ P) (h₂ : L₂ ≤ P) : Prop :=
    L₁.compositum L₂ ≤ P

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
