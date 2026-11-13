/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# NYLL M010: abstract fields finite over the distinguished base

Modified by Worker 171: extract M010.121 and M010.123–125 from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, prefix the
namespace with `Langlands.NYLL`, replace the source module imports by focused
published imports, and name the anonymous source instance
`Langlands.NYLL.PortInternal.M010.d125`. Universes, binders, structure fields,
bodies and proof terms are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-! ## Fields finite over the distinguished base -/

/-- An abstract field finite over the distinguished base field. -/
structure FiniteAbstractField (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field has finite degree over the distinguished base. -/
  finite : Finite ((baseField G).toSubgroup ⧸
    extensionSubgroup (baseField G) field (le_baseField field))

namespace FiniteAbstractField

/-- The distinguished base field, bundled with its trivial finite quotient. -/
noncomputable def base (G : Type u) [Group G] [TopologicalSpace G] :
    FiniteAbstractField G where
  field := baseField G
  finite := by
    let : (extensionSubgroup (baseField G) (baseField G)
        (le_baseField (baseField G))).Normal := by
      rw [show extensionSubgroup (baseField G) (baseField G)
          (le_baseField (baseField G)) = ⊤ by
        ext x
        exact Iff.rfl]
      infer_instance
    let : Subsingleton
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) (baseField G)
            (le_baseField (baseField G))) := by
      constructor
      intro x y
      refine Quotient.inductionOn₂' x y ?_
      intro a b
      apply QuotientGroup.eq_iff_div_mem.mpr
      exact Subgroup.mem_top _
    infer_instance

/-- Regard a finite abstract field as its finite extension of the
distinguished base field. -/
def toFiniteAbstractExtension (K : FiniteAbstractField G) :
    DegreeData.FiniteAbstractExtension G where
  field := K.field
  base := baseField G
  below := le_baseField K.field
  finiteQuotient := K.finite

/-- A finite abstract field supplies finiteness of its quotient over the distinguished base. -/
instance _root_.Langlands.NYLL.PortInternal.M010.d125 (K : FiniteAbstractField G) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field)) :=
  K.finite

end FiniteAbstractField

end
end Langlands.NYLL.ClassFormation
