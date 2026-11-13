/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions

/-!
# NYLL M010: finite abstract-extension core data

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

/-- A finite abstract extension.  Finiteness is carried by the extension
object, so its public numerical invariants can be positive naturals rather than
using the raw subgroup-index convention in which an infinite index is encoded
as `0`. -/
structure FiniteAbstractExtension (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension G where
  /-- The relative quotient of the base subgroup by the extension subgroup is finite. -/
  finiteQuotient :
    Finite
      (toAbstractExtension.base.toSubgroup ⧸
        (toAbstractExtension.field.toSubgroup.subgroupOf toAbstractExtension.base.toSubgroup))

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- The subgroup of the base represented by a finite extension. -/
def subgroup : Subgroup E.base.toSubgroup :=
  (E.field.toSubgroup.subgroupOf E.base.toSubgroup)

/-- The finite extension's actual relative coset space. -/
def quotient : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- Bundle an inclusion once its actual relative coset type is known to be
finite.  This is the canonical boundary from subgroup data to the finite
extension API; numerical invariants are obtained only from the resulting
object. -/
def ofInclusion (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [hfinite : Finite
      (base.toSubgroup ⧸ (field.toSubgroup.subgroupOf base.toSubgroup))] :
    FiniteAbstractExtension G where
  field := field
  base := base
  below := below
  finiteQuotient := hfinite

/-- The unramified predicate for a finite extension is the predicate on its
underlying abstract extension. -/
def IsUnramified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsUnramified D

/-- The totally ramified predicate for a finite extension is the predicate on
its underlying abstract extension. -/
def IsTotallyRamified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsTotallyRamified D

/-- The coset space carried by a finite abstract extension is finite. -/
instance quotientFinite :
    Finite E.quotient := by
  simpa [quotient, subgroup] using E.finiteQuotient

/-- The finite instance in the concrete quotient presentation used by norm
maps. -/
instance representedQuotientFinite :
    Finite
      (E.base.toSubgroup ⧸
        (E.field.toSubgroup.subgroupOf E.base.toSubgroup)) :=
  E.finiteQuotient

/-- The positive degree of a finite abstract extension. -/
def degree : ℕ+ :=
  by
    letI : Nonempty E.quotient :=
      ⟨QuotientGroup.mk 1⟩
    exact ⟨Nat.card E.quotient, Nat.card_pos⟩

end FiniteAbstractExtension

end DegreeData

end
end Langlands.NYLL.ClassFormation
