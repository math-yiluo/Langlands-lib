/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.GaloisGenerator.Definitions

/-!
# NYLL M084: the transported cyclic generator generates

Modified by Worker 224: extract the statement of M084.005 from the pinned
`FixedSource.lean`, prefix the namespace with `Langlands.NYLL`, append
`Statement`, and replace the theorem by a Prop-valued definition with its
original telescope and conclusion. The source proof is omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation.FiniteCyclicSubextension

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {K : FiniteAbstractField G}

/-- Target that the transported generator generates the whole finite Galois
quotient. -/
def galoisGenerator_generatesStatement (E : FiniteCyclicSubextension K) : Prop :=
  ∀ x, x ∈ Subgroup.zpowers E.galoisGenerator

end Langlands.NYLL.ClassFormation.FiniteCyclicSubextension

end
