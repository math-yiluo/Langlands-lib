/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions

/-!
# Target: the coercion of the right conjugate of a fixed element

Modified by Worker 5264, 15 November 2026: state the source theorem M026.004
`conjugateFixedElement_coe` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by the focused import of the
M026.003 definition, keep the source opens, variable declaration, binders
and statement, and omit the proof `rfl`, the `@[simp]` attribute and the
rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: establishes the identity `((conjugateFixedElement A K σ a :
ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) = A.ρ σ⁻¹ a.1`. -/
def conjugateFixedElement_coeStatement [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) : Prop :=
    ((conjugateFixedElement A K σ a :
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
      A.ρ σ⁻¹ a.1

end

end Langlands.NYLL.ClassFormation
