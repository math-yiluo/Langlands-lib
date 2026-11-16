/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Statements

/-!
# NYLL M026.008: absolute conjugation of a coset representative

Modified by Worker 5264, 15 November 2026: prove the published target
`absoluteConjugateCosetEquiv_mkStatement` (M026.008) by the source proof of
`absoluteConjugateCosetEquiv_mk` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, with the private source
definition `absoluteConjugationEquiv` (M026.005) written by its published
name `Langlands.NYLL.PortInternal.M026.d005`, replace the source imports by
the published statement module and omit the `@[simp]` attribute, the unused
opens and variables and the rest of the source file. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/--
Establishes the identity `absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) = QuotientGroup.mk
(absoluteConjugationEquiv σ x)`.
-/
theorem absoluteConjugateCosetEquiv_mk
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) :
    absoluteConjugateCosetEquiv_mkStatement K σ x := by
  show absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
    QuotientGroup.mk (Langlands.NYLL.PortInternal.M026.d005 σ x)
  rfl

end

end Langlands.NYLL.ClassFormation
