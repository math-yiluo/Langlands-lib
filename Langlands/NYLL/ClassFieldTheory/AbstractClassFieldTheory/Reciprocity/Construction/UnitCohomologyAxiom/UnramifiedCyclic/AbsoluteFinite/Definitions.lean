/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.UnramifiedCyclic.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs

/-!
# NYLL M032: the absolute quotient of a finite unramified cyclic extension is finite

Modified by Worker 5264, 15 November 2026: port the anonymous source
instance M032.014 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 under the name
`Langlands.NYLL.PortInternal.M032.d014`. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports
(the M032.009 structure with its instances and the proved M026.014
`relativeTowerQuotientFinite`), keep the source opens, variable
declarations, namespace, docstring, binders and body unchanged, and omit the
rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- The absolute quotient attached to a finite unramified cyclic extension is finite. -/
noncomputable instance _root_.Langlands.NYLL.PortInternal.M032.d014
    (E : FiniteUnramifiedCyclicExtension D K) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.field (le_baseField E.field)) :=
  relativeTowerQuotientFinite (baseField G) K.field E.field E.below
    (le_baseField K.field)

end FiniteUnramifiedCyclicExtension

end

end Langlands.NYLL.ClassFormation
