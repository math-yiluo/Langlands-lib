/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.CyclicSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions

/-!
# NYLL M084: the finite Galois presentation of a cyclic generator

Modified by Worker 224: extract M084.003 and M084.004 from the pinned
`FixedSource.lean`, prefix the namespace with `Langlands.NYLL`, and use focused
imports. The constructions and source universe-zero telescope are unchanged.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation.FiniteCyclicSubextension

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {K : FiniteAbstractField G}

/-- Forget only the chosen cyclic generator. The resulting finite Galois
bundle is the canonical input to the finite reciprocity construction. -/
def toFiniteGaloisSubextension (E : FiniteCyclicSubextension K) :
    FiniteGaloisSubextension K.field where
  field := E.field
  below := E.below
  normal := E.normal
  finite := E.finite

/-- The cyclic generator transported across the finite Galois quotient
boundary. -/
def galoisGenerator (E : FiniteCyclicSubextension K) :
    E.toFiniteGaloisSubextension.extensionQuotient :=
  E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.symm E.generator

end Langlands.NYLL.ClassFormation.FiniteCyclicSubextension

end
