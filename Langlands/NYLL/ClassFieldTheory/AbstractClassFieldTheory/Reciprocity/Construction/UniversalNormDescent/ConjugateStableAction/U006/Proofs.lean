/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Statements

/-!
# NYLL M043.006: the conjugation-stable action after coercion

Modified by Worker 5264, 15 November 2026: prove the published target
`conjugateStableAction_coeStatement` (M043.006) by the source proof of
`conjugateStableAction_coe` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type and
begin the proof with `show` stating it unfolded. Port the private source
helper `transport_fixed_coe` (M043.004), with its source statement and
proof, as a private theorem of this module. Replace the source imports by the
published statement module and omit the `@[simp]` attribute, the unused
universes and opens and the rest of the source file. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

private theorem transport_fixed_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl

/-- The conjugation-stable action agrees with its ambient action after coercion. -/
theorem conjugateStableAction_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) :
    conjugateStableAction_coeStatement B F s hF a := by
  show ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
    B.ρ s⁻¹ a.1
  exact transport_fixed_coe B _ F hF _

end

end Langlands.NYLL.ClassFormation
