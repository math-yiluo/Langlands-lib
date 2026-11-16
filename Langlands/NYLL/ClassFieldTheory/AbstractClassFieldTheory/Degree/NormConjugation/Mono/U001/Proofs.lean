/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation.Mono.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs

/-!
# NYLL M035.001: conjugation preserves inclusions of abstract fields

Modified by Worker 5264, 15 November 2026: prove the published target
`conjugateClosedSubgroup_monoStatement` (M035.001) by the source proof of
`conjugateClosedSubgroup_mono` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source
`rw [conjugateClosedSubgroup_mem] at hx ⊢` by `.mp`/`.mpr` of the published
`...Statement`-typed `conjugateClosedSubgroup_mem`, replace the source
imports by published modules and omit the unused opens and the rest of the
source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Conjugation preserves inclusions of abstract fields. -/
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    conjugateClosedSubgroup_monoStatement hLK s := by
  show (conjugateClosedSubgroup L s).toSubgroup ≤
    (conjugateClosedSubgroup K s).toSubgroup
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  exact (conjugateClosedSubgroup_mem K s x).mpr
    (hLK ((conjugateClosedSubgroup_mem L s x).mp hx))

end GroupOnly

end

end Langlands.NYLL.ClassFormation
