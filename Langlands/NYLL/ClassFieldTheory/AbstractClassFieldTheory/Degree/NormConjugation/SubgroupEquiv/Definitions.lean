/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs

/-!
# Conjugation of a field subgroup onto its right conjugate

Modified by Worker 5264, 15 November 2026: port the source definition
M035.002 `conjugateSubgroupEquiv` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by a focused published import
(the proved M026.002 `conjugateClosedSubgroup_mem`), keep the source
universe and variable declarations, the section `GroupOnly`, the docstring,
binders and data, and replace one `rw [conjugateClosedSubgroup_mem]` in a
membership proof by `refine (conjugateClosedSubgroup_mem K s _).2 ?_`,
because the published theorem has a Prop-valued Statement type. Omit the
unused opens and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Conjugation by `s⁻¹` identifies a field subgroup with the subgroup
representing its right conjugate `K^s`. -/
def conjugateSubgroupEquiv [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) :
    K.toSubgroup ≃* (conjugateClosedSubgroup K s).toSubgroup where
  toFun k := ⟨s⁻¹ * k.1 * s, by
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
    refine (conjugateClosedSubgroup_mem K s _).2 ?_
    convert k.2 using 1
    simp [mul_assoc]⟩
  invFun x := ⟨s * x.1 * s⁻¹,
    (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

end GroupOnly

end

end Langlands.NYLL.ClassFormation
