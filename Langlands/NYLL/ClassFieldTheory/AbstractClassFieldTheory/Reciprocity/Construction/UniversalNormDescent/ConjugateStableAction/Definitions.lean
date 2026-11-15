/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions

/-!
# The conjugation-stable action on fixed elements

Modified by Worker 5264, 15 November 2026: port the source definition
M043.003 `conjugateStableAction` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by the focused import of the
M026.003 definition `conjugateFixedElement`, keep the source universes,
opens, docstring, binders and body unchanged, and omit the rest of the
source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u v

namespace Langlands.NYLL.ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- Transport the ordinary conjugation action back to a field stabilized
by that conjugation. -/
noncomputable def conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : ambientFixedAddSubgroup B F :=
  hF ▸ conjugateFixedElement B F s a

end

end Langlands.NYLL.ClassFormation
