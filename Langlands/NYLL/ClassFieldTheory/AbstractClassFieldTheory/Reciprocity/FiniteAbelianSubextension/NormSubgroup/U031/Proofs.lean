/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U025.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.U019.Proofs

/-!
# NYLL M296.031: norm subgroups reverse finite abelian inclusion

Modified by Worker 507, 16 November 2026: extract M296.031 (source lines
421–449) from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, replace the source imports by the published target and the
two published prerequisite proofs, and state the conclusion through
`normSubgroup_antitoneStatement`. Omit unrelated declarations and the unused
`universe u`. The proof body is unchanged. The paired Markdown describes the
implemented proof and all adaptations. See `licenses/NYLL/LICENSE` and
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

/-- An inclusion of finite abelian subextensions reverses inclusion of their
relative-norm images in the fixed coefficient group. -/
theorem normSubgroup_antitone (A : Rep ℤ G)
    {L₁ L₂ : FiniteAbelianSubextension K} (h : L₁ ≤ L₂) :
    normSubgroup_antitoneStatement A h := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L₂.field L₂.below) := L₂.finite
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L₁.field L₁.below) := L₁.finite
  let hL₂L₁finite : Finite (L₁.field.toSubgroup ⧸
      extensionSubgroup L₁.field L₂.field h) :=
    FiniteGaloisSubextension.finite_extension_over_intermediate
      L₂.below L₁.below h
  let T : DegreeData.FiniteTower G := {
    top := L₂.field
    middle := L₁.field
    base := K
    top_le_middle := h
    middle_le_base := L₁.below
    finiteTopQuotient := by
      change Finite (L₁.field.toSubgroup ⧸
        extensionSubgroup L₁.field L₂.field h)
      exact hL₂L₁finite
    finiteBaseQuotient := L₁.finite }
  change finiteNormSubgroup A K L₂.field L₂.below ≤
    finiteNormSubgroup A K L₁.field L₁.below
  rintro _ ⟨a, rfl⟩
  refine ⟨relativeNorm A L₁.field L₂.field h a, ?_⟩
  exact T.norm_trans_apply A a

end FiniteAbelianSubextension

end Representation

end Langlands.NYLL.ClassFormation
