/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericDefinitions

/-!
# NYLL M330.005: absolute and relative residue-degree target

Modified by Worker 317: extract the statement of M330.005 from the pinned
NYLL `AbstractUnramified.lean`, prefix the namespace with `Langlands.NYLL`,
and replace the theorem by a Prop-valued definition with the suffix
`Statement`. Use the two focused published imports above and omit the proof
and all other source declarations. The source telescope and equality are
unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.ClassFormation

universe u

/-- For a field finite over the distinguished abstract base, the absolute
residue degree agrees with its relative residue degree over that base. -/
def finiteAbstractField_residueDegree_eq_relativeResidueDegreeStatement
    {G : Type u} [Group G] [TopologicalSpace G]
    (D : DegreeData G) (H : FiniteAbstractField G) : Prop :=
  (H.residueDegree D : ℕ) =
    (H.toFiniteAbstractExtension.residueDegree D : ℕ)

end Langlands.NYLL.LocalClassFieldTheory
