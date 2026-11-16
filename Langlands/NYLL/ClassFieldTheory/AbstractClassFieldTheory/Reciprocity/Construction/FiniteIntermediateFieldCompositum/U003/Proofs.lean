/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Definitions

/-!
# NYLL M037.003: a common finite stage below finitely many finite stages

Modified by Worker 5264, 15 November 2026: prove the published target
`FiniteIntermediateField.exists_common_compositumStatement` (M037.003) by the
source proof of `FiniteIntermediateField.exists_common_compositum` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, and state the bounds
`compositum_le_left` and `compositum_le_right` (M034.002, M034.003, whose
proofs are not yet in the Library) by their source proofs `inf_le_left` and
`inf_le_right` as the local facts `hleft` and `hright`, used in their place.
Replace the source import by the published statement and compositum
definition modules, omit the source's unused `open`s and the rest of the
source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u v

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- An initial finite stage and finitely many further stages have a common
finite overfield.  This existential form avoids choosing an artificial
ordering of the finite family. -/
theorem exists_common_compositum {E K : ClosedSubgroup G} {ι : Type v}
    (M : FiniteIntermediateField E K) (s : Finset ι)
    (F : ι → FiniteIntermediateField E K) :
    exists_common_compositumStatement M s F := by
  show ∃ P : FiniteIntermediateField E K,
    P.field.toSubgroup ≤ M.field.toSubgroup ∧
      ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup
  have hleft : ∀ P N : FiniteIntermediateField E K,
      (P.compositum N).field.toSubgroup ≤ P.field.toSubgroup :=
    fun P N => inf_le_left
  have hright : ∀ P N : FiniteIntermediateField E K,
      (P.compositum N).field.toSubgroup ≤ N.field.toSubgroup :=
    fun P N => inf_le_right
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨M, le_rfl, fun i hi => (Finset.notMem_empty i hi).elim⟩
  | @insert i s hi ih =>
      rcases ih with ⟨P, hPM, hPF⟩
      let Q := P.compositum (F i)
      refine ⟨Q, (hleft P (F i)).trans hPM, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with hji | hj
      · simpa [hji] using hright P (F i)
      · exact (hleft P (F i)).trans (hPF j hj)

end FiniteIntermediateField

end finiteIntermediateFields

end

end Langlands.NYLL.ClassFormation
