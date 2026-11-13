/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# NYLL M010: finite-residue extension core data

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

/-- A finite extension whose base and field both carry their honest finite
absolute residue quotients.  The proof-dependent relative quotient is stored
once in the object and exposed through `toFiniteAbstractExtension`. -/
structure FiniteResidueAbstractExtension (D : DegreeData G) where
  /-- The top endpoint with its finite residue quotient. -/
  field : FiniteResidueAbstractField D
  /-- The base endpoint with its finite residue quotient. -/
  base : FiniteResidueAbstractField D
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        (field.field.toSubgroup.subgroupOf base.field.toSubgroup))

namespace FiniteResidueAbstractExtension

variable {D : DegreeData G}

/-- Forget only the endpoint residue-finiteness data. -/
def toFiniteAbstractExtension (E : FiniteResidueAbstractExtension D) :
    FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- A finite-residue extension supplies finiteness of its represented relative quotient. -/
instance _root_.Langlands.NYLL.PortInternal.M010.d114 (E : FiniteResidueAbstractExtension D) :
    Finite
      (E.base.field.toSubgroup ⧸
        (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)) :=
  E.finiteQuotient

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

end FiniteResidueAbstractExtension

end DegreeData

end
end Langlands.NYLL.ClassFormation
