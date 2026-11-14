/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs

/-!
# The maximal-unramified degree equivalence and the Frobenius

Modified by Worker 5264: extract M011.012 `maximalUnramifiedDegreeEquiv` and
M011.014 `frobenius` from the pinned NYLL Frobenius source with the
Langlands.NYLL namespace prefix. The source-private theorem M011.011
`fieldInertiaWithin_le_normalizedDegree_ker`, which the body of M011.012 cites
twice, is replaced by a local hypothesis with the same statement, proved from
the published theorem M011.010 `normalizedDegree_ker`, as in the source proof.
The two source rewrites with M011.010 inside the injectivity proof use that
theorem through a local equation. The source import of the whole Fields module
is replaced by the published proofs of M011.009 and M011.010. The source
variable declaration, docstrings, signatures and remaining construction bodies
are retained. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The isomorphism `d_K : G(\widetilde K|K) ≃ ℤ̂`. -/
def maximalUnramifiedDegreeEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) ≃* ZHatMul := by
  have hker : (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field :=
    D.normalizedDegree_ker K
  have hle : D.fieldInertiaWithin K.field ≤ (D.normalizedDegree K).toMonoidHom.ker := by
    rw [hker]
  let dquot : (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →* ZHatMul :=
    QuotientGroup.lift (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      hle
  apply MulEquiv.ofBijective dquot
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply QuotientGroup.eq.mpr
    change a⁻¹ * b ∈ D.fieldInertiaWithin K.field
    rw [← hker]
    change D.normalizedDegree K (a⁻¹ * b) = 1
    rw [map_mul, map_inv]
    have hab' : D.normalizedDegree K a = D.normalizedDegree K b := by
      simpa [dquot] using hab
    rw [hab', inv_mul_cancel]
  · exact QuotientGroup.lift_surjective_of_surjective
      (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      (D.normalizedDegree_surjective K)
      hle

/-- **the normalized Frobenius definition.** The Frobenius over `K`, characterized by
`d_K(φ_K)=1`. -/
def frobenius (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field :=
  (D.maximalUnramifiedDegreeEquiv K).symm
    (Multiplicative.ofAdd (1 : ZHat))

end DegreeData

end
end Langlands.NYLL.ClassFormation
