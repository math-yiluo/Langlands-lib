/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions

/-!
# NYLL M296: elementary finite abelian subextension targets

Modified by Worker 159, 13 November 2026: extract the asserted types of the
source theorems M296.011–.013 (lines 110–142) of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709` as Prop-valued definitions without
their proofs. Prefix the namespace with `Langlands.NYLL`, append `Statement` to
each theorem name, drop the `@[simp]` and `@[ext]` attributes (they belong to the
later proofs) and import the published M296 data module. The paired Markdown
records every modification. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- Target of `FiniteAbelianSubextension.extensionQuotientMk_apply`: the named
abelian quotient projection agrees with the underlying quotient map. -/
def extensionQuotientMk_applyStatement (L : FiniteAbelianSubextension K)
    (k : K.toSubgroup) : Prop :=
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below)

-- Preserve the source hypothesis names even when the conclusion does not
-- mention them.
set_option linter.unusedVariables false in
/-- Target of `FiniteAbelianSubextension.extensionQuotient_inductionOn`:
eliminate an abelian extension quotient without choosing a representative. -/
protected def extensionQuotient_inductionOnStatement
    (L : FiniteAbelianSubextension K)
    {motive : L.extensionQuotient → Prop} (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) : Prop :=
    motive q

set_option linter.unusedVariables false in
/-- Target of `FiniteAbelianSubextension.ext`: two packages with the same
closed subgroup represent the same finite abelian extension. -/
def extStatement {L₁ L₂ : FiniteAbelianSubextension K}
    (h : L₁.field = L₂.field) : Prop :=
  L₁ = L₂

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
