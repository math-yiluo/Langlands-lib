/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# NYLL M010: total-ramification image criteria

Modified by Worker 357: extract M010.064 and M010.076, prefix their namespace
with Langlands.NYLL, replace source imports with focused published imports,
and turn theorems into Prop-valued targets without their proofs.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Total ramification is characterized by containment of degree images. -/
def isTotallyRamified_iff_image_leStatement (L : GaloisSubextension K)
    (D : DegreeData G) : Prop :=
  L.IsTotallyRamified D ↔
    K.toSubgroup.map D.degree.toMonoidHom ≤
      L.field.toSubgroup.map D.degree.toMonoidHom

end GaloisSubextension

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- Finite total ramification is characterized by containment of degree images. -/
def isTotallyRamified_iff_image_leStatement (D : DegreeData G) : Prop :=
  E.IsTotallyRamified D ↔
    E.base.toSubgroup.map D.degree.toMonoidHom ≤
      E.field.toSubgroup.map D.degree.toMonoidHom

end FiniteAbstractExtension

end DegreeData
end Langlands.NYLL.ClassFormation
