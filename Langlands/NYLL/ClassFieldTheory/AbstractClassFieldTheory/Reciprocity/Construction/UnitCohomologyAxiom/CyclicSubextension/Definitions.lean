/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# NYLL M032: finite cyclic subextensions of a finite abstract field

Modified by Worker 5424: extract M032.001-004, M032.006-008 and M032.016 from
the pinned NYLL UnitCohomologyAxiom.lean, prefix the namespace with
Langlands.NYLL, give the anonymous instances their PortInternal names and use
focused published imports. The declarations, binders and bodies are otherwise
unchanged. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

open CategoryTheory

universe u

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite cyclic extension of a bundled finite abstract field.  The
generator and its cyclicity proof travel with the finite normal extension. -/
structure FiniteCyclicSubextension (K : FiniteAbstractField G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.field.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (extensionSubgroup K.field field below).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.field.toSubgroup ⧸
    extensionSubgroup K.field field below)
  /-- A chosen generator of the relative Galois quotient. -/
  generator : K.field.toSubgroup ⧸ extensionSubgroup K.field field below
  /-- Every quotient element is a power of the chosen generator. -/
  generates : ∀ x, x ∈ Subgroup.zpowers generator

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- Forget the cyclic generator and normality, retaining the underlying finite
abstract extension. -/
@[implicit_reducible]
def toFiniteAbstractExtension (E : FiniteCyclicSubextension K) :
    DegreeData.FiniteAbstractExtension G where
  field := E.field
  base := K.field
  below := E.below
  finiteQuotient := E.finite

/-- Structural unramifiedness of the underlying finite extension. -/
def IsUnramified (E : FiniteCyclicSubextension K) (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension. -/
def IsTotallyRamified (E : FiniteCyclicSubextension K)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

/-- A finite cyclic subextension supplies normality of its representing subgroup. -/
instance _root_.Langlands.NYLL.PortInternal.M032.d006 (E : FiniteCyclicSubextension K) :
    (extensionSubgroup K.field E.field E.below).Normal :=
  E.normal

/-- A finite cyclic subextension supplies finiteness of its Galois quotient. -/
instance _root_.Langlands.NYLL.PortInternal.M032.d007 (E : FiniteCyclicSubextension K) :
    Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  E.finite

/-- The finite quotient of a cyclic subextension carries its canonical `Fintype`. -/
noncomputable instance _root_.Langlands.NYLL.PortInternal.M032.d008
    (E : FiniteCyclicSubextension K) :
    Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  Fintype.ofFinite _

end FiniteCyclicSubextension

end Generic

section IntegralRep

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- The fixed coefficient representation attached to a bundled cyclic
extension. -/
noncomputable def fixedRepresentation (E : FiniteCyclicSubextension K)
    (A : Rep ℤ G) :
    Rep ℤ (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  extensionFixedRepresentation A K.field E.field E.below E.normal

end FiniteCyclicSubextension

end IntegralRep

end
end Langlands.NYLL.ClassFormation
