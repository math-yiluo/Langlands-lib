/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements

/-!
# Cardinality of the NYLL residue quotient

Modified by Worker 289: extract source unit M010.019, prefix the namespace
with Langlands.NYLL, and use the published Statement as the result type.
Replace the source import list by the focused target import. Retain the
original reflexivity proof and simp attribute.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation.DegreeData

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The cardinal residue degree is the cardinality of the concrete residue quotient. -/
@[simp] theorem residueDegreeCardinal_eq_mk_residueQuotient
    (D : DegreeData G) (K : ClosedSubgroup G) :
    residueDegreeCardinal_eq_mk_residueQuotientStatement D K :=
  rfl

end Langlands.NYLL.ClassFormation.DegreeData
