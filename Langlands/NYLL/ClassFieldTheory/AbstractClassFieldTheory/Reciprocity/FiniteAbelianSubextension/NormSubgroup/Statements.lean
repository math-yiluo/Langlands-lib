/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Compositum

/-!
# NYLL M296: order targets for finite abelian norm subgroups

Modified by Worker 449, 14 November 2026: extract the asserted types of the
source theorems M296.031 and M296.032 (lines 423–425 and 453–456) of the pinned
NYLL `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709` as Prop-valued definitions
without their proofs. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to each theorem name, drop the unused `universe u` and import the
published M296 norm-subgroup, order and compositum modules. The paired
Markdown records every modification. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology KummerTheory

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

-- Preserve the source hypothesis name even though the conclusion does not
-- mention it.
set_option linter.unusedVariables false in
/-- Target of `FiniteAbelianSubextension.normSubgroup_antitone`. The
source-level implication in the order formula: an inclusion of fields gives
the reverse inclusion of norm subgroups. -/
def normSubgroup_antitoneStatement (A : Rep ℤ G)
    {L₁ L₂ : FiniteAbelianSubextension K} (h : L₁ ≤ L₂) : Prop :=
    normSubgroup A L₂ ≤ normSubgroup A L₁

/-- Target of `FiniteAbelianSubextension.normSubgroup_compositum_le_inf`. The
unconditional half of `N_{L₁L₂} = N_{L₁} ∩ N_{L₂}` in the finite abelian
class-field classification. -/
def normSubgroup_compositum_le_infStatement (A : Rep ℤ G)
    (L₁ L₂ : FiniteAbelianSubextension K) : Prop :=
    normSubgroup A (L₁.compositum L₂) ≤
      normSubgroup A L₁ ⊓ normSubgroup A L₂

end FiniteAbelianSubextension

end Representation

end Langlands.NYLL.ClassFormation
