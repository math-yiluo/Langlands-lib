/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U008.Proofs

/-!
# NYLL M011.010: the normalized degree kernel

Modified by Worker 499: extract source unit M011.010 from the pinned NYLL
Frobenius source, prefix the namespace with Langlands.NYLL, replace the broad
source import with focused imports, and conclude the exact published Statement
target. Add a leading `show` to expose the target; keep the remaining source proof unchanged.
The focused proof adaptation was supplied and checked by Worker 5264.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The kernel of `d_K` is the inertia group `I_K`. -/
theorem normalizedDegree_ker (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    normalizedDegree_kerStatement D K := by
  show (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field
  ext k
  constructor
  · intro hk
    change D.degree k.1 = 1
    apply Multiplicative.ext
    rw [← D.residueDegree_nsmul_normalizedDegree K k]
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd = 0
    rw [show D.normalizedDegree K k = 1 from hk]
    simp only [toAdd_one, nsmul_zero]
  · intro hk
    apply Multiplicative.ext
    apply zHatMulNat_injective K.residueDegree.property
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
      (K.residueDegree : ℕ) • (1 : ZHatMul).toAdd
    rw [D.residueDegree_nsmul_normalizedDegree K k]
    rw [show D.degree k.1 = 1 from hk]
    simp only [toAdd_one, nsmul_zero]

end DegreeData

end
end Langlands.NYLL.ClassFormation
