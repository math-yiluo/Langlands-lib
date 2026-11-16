/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Statements

/-!
# NYLL M026.004: the coercion of the right conjugate of a fixed element

Modified by Worker 5264, 15 November 2026: prove the published target
`conjugateFixedElement_coeStatement` (M026.004) by the source proof of
`conjugateFixedElement_coe` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source imports
by the published statement module and omit the `@[simp]` attribute, the
unused opens and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/--
Establishes the identity `((conjugateFixedElement A K σ a : ambientFixedAddSubgroup A
(conjugateClosedSubgroup K σ)) : A.V) = A.ρ σ⁻¹ a.1`.
-/
theorem conjugateFixedElement_coe [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    conjugateFixedElement_coeStatement A K σ a := by
  show ((conjugateFixedElement A K σ a :
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
    A.ρ σ⁻¹ a.1
  rfl

end

end Langlands.NYLL.ClassFormation
