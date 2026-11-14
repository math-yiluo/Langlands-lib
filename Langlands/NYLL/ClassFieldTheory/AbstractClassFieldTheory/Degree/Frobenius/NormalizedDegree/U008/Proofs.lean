/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Statements
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs

/-!
# NYLL M011.008: the normalized degree identity

Modified by Worker 499: extract source unit M011.008 from the pinned NYLL
Frobenius source, prefix the namespace with Langlands.NYLL, replace the broad
source import with focused imports, and conclude the exact published Statement
target. Keep the source proof body unchanged.
The focused proof adaptation was supplied and checked by Worker 5264.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The defining identity `f_K d_K = d`. -/
theorem residueDegree_nsmul_normalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    residueDegree_nsmul_normalizedDegreeStatement D K k := by
  exact zHatMulNat_zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
    (D.restrictedDegreeInMulNatRange K k)

end DegreeData

end
end Langlands.NYLL.ClassFormation
