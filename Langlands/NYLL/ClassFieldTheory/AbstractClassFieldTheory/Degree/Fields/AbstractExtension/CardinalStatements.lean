/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.Definitions

/-!
# NYLL M010: abstract-extension cardinal targets

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

namespace AbstractExtension

def degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinalStatement
    (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.degreeCardinal =
      Cardinal.lift.{u} (E.relativeResidueDegreeCardinal D) *
        E.relativeRamificationIndexCardinal D

def relativeResidueDegreeCardinal_mul_residueDegreeCardinalStatement
    (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.relativeResidueDegreeCardinal D * D.residueDegreeCardinal E.base =
      D.residueDegreeCardinal E.field

end AbstractExtension
end DegreeData

end
end Langlands.NYLL.ClassFormation
