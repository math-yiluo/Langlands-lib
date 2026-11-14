/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions

/-!
# Target: naturality of the normalized degree along a finite extension

Modified by Worker 5264: extract the public theorem signature M011.019
`frobeniusRestrictionNaturality_normalizedDegree` from the pinned NYLL
Frobenius source as a Prop-valued Statement definition. Prefix the namespace
with Langlands.NYLL, append `Statement` to the name, keep the source variable
declaration, parameters and binder kinds, use focused published imports, and
omit the proof.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: **Frobenius residue-degree compatibility (commutative square).** On `G_L`, the
normalized degree maps satisfy `d_K = f_{L|K} d_L`. -/
def frobeniusRestrictionNaturality_normalizedDegreeStatement (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (l : E.field.field.toSubgroup) : Prop :=
  (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
    (E.residueDegree : ℕ) •
      (D.normalizedDegree E.field l).toAdd

end DegreeData

end

end Langlands.NYLL.ClassFormation
