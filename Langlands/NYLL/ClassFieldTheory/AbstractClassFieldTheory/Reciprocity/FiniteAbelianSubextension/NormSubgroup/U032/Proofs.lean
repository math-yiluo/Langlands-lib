/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.U031.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.M296018Proof
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.M296019Proof

/-!
# NYLL M296.032: compositum norms lie in both norm subgroups

Modified by Worker 275, 16 November 2026: extract M296.032 (source lines
451–459) from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, and import the published target and prerequisite proofs.
Express the conclusion as the target applied to the same source arguments.
The proof body is unchanged. Omit the unused source universe declaration.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology KummerTheory

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The unconditional half of
`N_{L₁L₂} = N_{L₁} ∩ N_{L₂}` in the finite abelian class-field classification. -/
theorem normSubgroup_compositum_le_inf (A : Rep ℤ G)
    (L₁ L₂ : FiniteAbelianSubextension K) :
    normSubgroup_compositum_le_infStatement A L₁ L₂ := by
  intro x hx
  exact ⟨normSubgroup_antitone A (le_compositum_left L₁ L₂) hx,
    normSubgroup_antitone A (le_compositum_right L₁ L₂) hx⟩

end FiniteAbelianSubextension

end Representation

end Langlands.NYLL.ClassFormation
