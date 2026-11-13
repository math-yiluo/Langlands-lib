/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions

/-!
# NYLL M010: finite extensions between fields finite over the base

Modified by Worker 171: extract M010.130 and M010.132–135 and M010.139 from the
pinned NYLL `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
prefix the namespace with `Langlands.NYLL`, replace the source module imports
by the focused published import, and name the anonymous source instance
`Langlands.NYLL.PortInternal.M010.d139`. Universes, binders, attributes,
structure fields and bodies are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite extension between two fields that are themselves finite over the
distinguished base.  Both endpoint finiteness proofs and the relative quotient
belong to the object. -/
structure FiniteAbstractFieldExtension (G : Type u)
    [Group G] [TopologicalSpace G] where
  /-- The top endpoint, finite over the distinguished base. -/
  field : FiniteAbstractField G
  /-- The base endpoint, finite over the distinguished base. -/
  base : FiniteAbstractField G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field.field below)

namespace FiniteAbstractFieldExtension

/-- Forget endpoint finiteness over the distinguished base. -/
@[implicit_reducible]
def toFiniteAbstractExtension (E : FiniteAbstractFieldExtension G) :
    DegreeData.FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- Structural unramifiedness of the represented relative extension. -/
@[implicit_reducible]
def IsUnramified (E : FiniteAbstractFieldExtension G) (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the represented relative extension. -/
def IsTotallyRamified (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteAbstractFieldExtension G) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

/-- A finite abstract field extension supplies finiteness of its relative quotient. -/
instance _root_.Langlands.NYLL.PortInternal.M010.d139 (E : FiniteAbstractFieldExtension G) :
    Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
  E.finiteQuotient

end FiniteAbstractFieldExtension

end
end Langlands.NYLL.ClassFormation
