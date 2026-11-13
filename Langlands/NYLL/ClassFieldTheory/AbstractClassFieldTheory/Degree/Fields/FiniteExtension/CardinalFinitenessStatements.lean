/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# NYLL M010: finite relative cardinal targets

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

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

def _root_.Langlands.NYLL.PortInternal.M010.d081Statement
    (D : DegreeData G) : Prop :=
  E.toAbstractExtension.relativeResidueDegreeCardinal D <
      Cardinal.aleph0

def _root_.Langlands.NYLL.PortInternal.M010.d082Statement
    (D : DegreeData G) : Prop :=
  E.toAbstractExtension.relativeRamificationIndexCardinal D <
      Cardinal.aleph0

end FiniteAbstractExtension
end DegreeData

end
end Langlands.NYLL.ClassFormation
