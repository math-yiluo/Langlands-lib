/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.AbsoluteBase.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs

/-!
# Normality of finite abelian subextensions over the absolute base

Adapted by Worker 666 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M300.002, lines 48–75
of `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`.
The theorem proves the published proposition target with its complete source
telescope. Membership in `extensionSubgroup` is used definitionally in place
of the source's membership-lemma rewrites. The paired Markdown records the
proof and all modifications. Original license and notices are retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

/-- Normality over the concrete ground-field fixing group is normality over
the abstract class-formation `baseField`. -/
theorem finiteAbelianSubextension_normal_over_absoluteBase
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianSubextension_normal_over_absoluteBaseStatement K L := by
  refine { conj_mem := fun h hh g ↦ ?_ }
  change (h : intrinsicAbsoluteGalois K) ∈ L.field at hh
  let h' : (intrinsicAbstractBase K).toSubgroup := ⟨h, L.below hh⟩
  let g' : (intrinsicAbstractBase K).toSubgroup := ⟨g, by
    rw [show intrinsicAbstractBase K =
        baseField (intrinsicAbsoluteGalois K) from
      closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)]
    exact g.property⟩
  exact L.normal.conj_mem h' hh g'

end Langlands.NYLL.LocalClassFieldTheory
