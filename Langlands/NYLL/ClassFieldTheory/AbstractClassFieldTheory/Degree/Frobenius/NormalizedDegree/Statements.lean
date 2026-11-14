/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions

/-!
# Targets for the normalized degree map

Modified by Worker 5264: extract the public theorem signatures M011.008
`residueDegree_nsmul_normalizedDegree`, M011.009 `normalizedDegree_surjective`
and M011.010 `normalizedDegree_ker` from the pinned NYLL Frobenius source as
Prop-valued Statement definitions. Prefix the namespace with Langlands.NYLL,
append `Statement` to each name, keep the source variable declaration,
parameters and binder kinds, and omit the proofs.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the defining identity `f_K d_K = d`. -/
def residueDegree_nsmul_normalizedDegreeStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) : Prop :=
  (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
    (D.degree k.1).toAdd

/-- Target: the normalized map is surjective, exactly as asserted before the
normalized Frobenius definition. -/
def normalizedDegree_surjectiveStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) : Prop :=
  Function.Surjective (D.normalizedDegree K)

/-- Target: the kernel of `d_K` is the inertia group `I_K`. -/
def normalizedDegree_kerStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) : Prop :=
  (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field

end DegreeData

end
end Langlands.NYLL.ClassFormation
