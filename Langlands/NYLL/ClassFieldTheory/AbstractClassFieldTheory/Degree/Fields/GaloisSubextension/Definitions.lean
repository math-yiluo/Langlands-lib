/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions

/-!
# NYLL M010: Galois subextension data

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

/-- A (not necessarily finite) Galois extension above `K`.  Normality and
the inclusion of the upper field are carried by the object, while no
finiteness assumption is introduced. -/
structure GaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The relative subgroup is normal in the base-field subgroup. -/
  normal : ((field.toSubgroup.subgroupOf K.toSubgroup)).Normal

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget normality while retaining the underlying abstract extension. -/
def toAbstractExtension (L : GaloisSubextension K) :
    DegreeData.AbstractExtension G where
  field := L.field
  base := K
  below := L.below

/-- The actual quotient represented by a Galois subextension.  This is a
named object boundary rather than a transparent abbreviation. -/
def extensionQuotient (L : GaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup)

/-- Structural unramifiedness of a Galois subextension. -/
def IsUnramified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsUnramified D

/-- Structural total ramification of a Galois subextension. -/
def IsTotallyRamified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsTotallyRamified D

/-- A Galois subextension has a normal subgroup inside its base subgroup. -/
instance extensionSubgroup_normalInstance (L : GaloisSubextension K) :
    ((L.field.toSubgroup.subgroupOf K.toSubgroup)).Normal :=
  L.normal

/-- The group structure transported across the named quotient boundary. -/
instance extensionQuotient_groupInstance (L : GaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup))
  infer_instance

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : GaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup)) :=
  MulEquiv.refl _

/-- The canonical quotient projection for a Galois subextension. -/
def extensionQuotientMk (L : GaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' ((L.field.toSubgroup.subgroupOf K.toSubgroup))

end GaloisSubextension

end DegreeData

end
end Langlands.NYLL.ClassFormation
