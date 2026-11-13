/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericDefinitions

/-!
# NYLL M010: finite-residue extension relative residue degree

Modified by Worker 198: extract the source units listed in the paired Markdown,
prefix their namespace with Langlands.NYLL, and use focused published imports.
The Markdown records all statement conversions and construction substitutions.
See licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace FiniteResidueAbstractExtension

variable {D : DegreeData G}

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

end FiniteResidueAbstractExtension
end DegreeData

end
end Langlands.NYLL.ClassFormation
