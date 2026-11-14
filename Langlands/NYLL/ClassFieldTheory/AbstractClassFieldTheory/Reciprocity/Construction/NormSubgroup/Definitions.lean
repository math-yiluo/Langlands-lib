/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# NYLL M029: finite intermediate fields and the maximal unramified field

Modified by Worker 483: extract M029.001, M029.002 and M029.016 from the
pinned NYLL NormSubgroup.lean, prefix the namespace with Langlands.NYLL and
use focused published imports. Omit the infinite-norm section and the
intervening theorems. The declarations, binders, universes, structure fields
and bodies (including the proof field of `base`) are otherwise unchanged.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite intermediate field `M` of an abstract extension `E | K`.
Contravariantly, its subgroup lies between `G_E` and `G_K`. -/
structure FiniteIntermediateField (E K : ClosedSubgroup G) where
  /-- The closed subgroup representing the intermediate field. -/
  field : ClosedSubgroup G
  /-- The extension endpoint lies below the intermediate-field subgroup. -/
  above : E.toSubgroup ≤ field.toSubgroup
  /-- The intermediate-field subgroup lies below the base endpoint. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The intermediate field has finite degree over the base endpoint. -/
  finite : Finite
    (K.toSubgroup ⧸ extensionSubgroup K field below)

namespace FiniteIntermediateField

/-- The base field itself is a finite intermediate field. -/
def base (E K : ClosedSubgroup G) (hEK : E.toSubgroup ≤ K.toSubgroup) :
    FiniteIntermediateField E K where
  field := K
  above := hEK
  below := le_rfl
  finite := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        exact x.2
    rw [htop]
    infer_instance

end FiniteIntermediateField

end finiteIntermediateFields

section maximalUnramifiedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The maximal unramified extension `\widetilde L`, represented by
`I_L = G_L ∩ ker(d)`. -/
def maximalUnramifiedField (D : DegreeData G) (L : ClosedSubgroup G) :
    ClosedSubgroup G :=
  D.fieldInertia L

end DegreeData

end maximalUnramifiedFields

end
end Langlands.NYLL.ClassFormation
