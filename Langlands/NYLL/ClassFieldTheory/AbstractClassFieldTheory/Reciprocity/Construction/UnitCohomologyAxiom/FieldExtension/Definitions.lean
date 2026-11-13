/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.UnramifiedCyclic.Definitions

/-!
# NYLL M032: the finite field-extension bundles of cyclic subextensions

Modified by Worker 5424: extract M032.005 and M032.010 from the pinned NYLL
UnitCohomologyAxiom.lean, prefix the namespace with Langlands.NYLL and use
focused published imports. The declarations, attributes, binders and bodies
are otherwise unchanged. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

open CategoryTheory

universe u

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- Retain the finite-over-base endpoint bundles as well as the relative
finite quotient. -/
@[implicit_reducible]
noncomputable def toFiniteAbstractFieldExtension
    (E : FiniteCyclicSubextension K) : FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
    E.finite
  exact FiniteAbstractFieldExtension.ofInclusion E.field K E.below

end FiniteCyclicSubextension

end Generic

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- Forget cyclic and unramified structure while retaining both finite
endpoint fields and the relative finite quotient. -/
@[implicit_reducible]
noncomputable def toFiniteAbstractFieldExtension
    (E : FiniteUnramifiedCyclicExtension D K) :
    FiniteAbstractFieldExtension G :=
  E.toFiniteCyclicSubextension.toFiniteAbstractFieldExtension

end FiniteUnramifiedCyclicExtension

end
end Langlands.NYLL.ClassFormation
