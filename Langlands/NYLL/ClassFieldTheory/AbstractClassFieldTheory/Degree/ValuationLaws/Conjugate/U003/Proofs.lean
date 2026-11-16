/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Conjugate.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FieldImageConjugate.U001.Proofs

/-!
# NYLL M027.003: conjugation preserves the residue degree of a residue-finite field

Modified by Worker 5264, 15 November 2026: prove the target
`DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement`
(M027.003) by the source proof of
`DegreeData.FiniteResidueAbstractField.residueDegree_conjugate` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the target proposition as its type and
begin the proof with `show` stating it unfolded. Replace the source imports
by the target's statement module and omit the source opens and variable
declarations, which this theorem does not use, and the rest of the source
file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Modified by Worker 743, 16 November 2026: import the published proof of
`DegreeData.fieldImage_conjugate` (M027.001), now in the Library, in place
of the private copy of its source proof; since that theorem has the
`...Statement` type `DegreeData.fieldImage_conjugateStatement`, the local
fact `himage` is stated with its unfolded equation.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Conjugation preserves the positive absolute residue degree at the
residue-finite boundary. -/
theorem DegreeData.FiniteResidueAbstractField.residueDegree_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement
      K σ := by
  show (K.conjugate σ).residueDegree = K.residueDegree
  apply PNat.eq
  change Nat.card
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) =
    Nat.card (D.residueQuotient K.field)
  unfold DegreeData.residueQuotient
  have himage : D.fieldImage (conjugateClosedSubgroup K.field σ) =
      D.fieldImage K.field :=
    D.fieldImage_conjugate K.field σ
  apply Nat.card_congr
  exact Subgroup.quotientEquivOfEq
    (congrArg
      (fun H : Subgroup ZHatMul => H.subgroupOf (⊤ : Subgroup ZHatMul))
      himage)

end

end Langlands.NYLL.ClassFormation
