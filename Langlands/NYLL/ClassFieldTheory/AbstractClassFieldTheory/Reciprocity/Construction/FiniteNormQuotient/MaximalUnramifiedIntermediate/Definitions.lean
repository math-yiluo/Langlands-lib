/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions

/-!
# A finite field as a finite intermediate field over its maximal unramified field

Modified by Worker 5264, 15 November 2026: port the source definition
M039.018 `DegreeData.fieldAsMaximalUnramifiedIntermediate` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL` and replace the source imports by the published module of
finite intermediate fields and the maximal unramified field. The proof
`D.maximalUnramifiedField_le L` (M029.019) of the field `above` is not
published; it is replaced by the final step `inf_le_left` of its source
proof, stated with `show`. That source proof first rewrites with M029.017
`maximalUnramifiedField_eq_fieldInertia`, a `rfl` theorem; here the goal is
checked by definitional unfolding instead (`D.maximalUnramifiedField L` is
`D.fieldInertia L`, which is `L ⊓ D.inertia`). The field is a proof, so by
proof irrelevance the structure is the source one. The docstring, the
universe, the binders and the other fields are unchanged. Omit the unused open `KummerTheory` and the rest of the
source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section finiteIntermediateField

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `L` itself is a finite intermediate field of `\widetilde L | K`. -/
def fieldAsMaximalUnramifiedIntermediate (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteIntermediateField (D.maximalUnramifiedField L) K where
  field := L
  above := show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
    inf_le_left
  below := hLK
  finite := hfinite

end DegreeData

end finiteIntermediateField

end
end Langlands.NYLL.ClassFormation
