/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U009.Definitions

/-!
# Reduction modulo `f` of the normalized degree, and its kernel

Modified by Worker 114: extract M301.001–.002 from the pinned NYLL
ValuationContinuity source, prefix the namespace with Langlands.NYLL, and
replace the three broad source imports by the focused published definitions
they use. Retain the source universe, section variables, parameter order,
binder kinds, docstrings, bodies and noncomputable section.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Reduction modulo `f` after the normalized degree `d_K`. -/
def unramifiedDegreeHom (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    K.toSubgroup →ₜ* Multiplicative (ZMod f) :=
  (zHatReductionMul f hf).comp (D.normalizedDegree K)

/-- The subgroup of `G_K` fixing the degree-`f` unramified extension. -/
def unramifiedDegreeKernelWithin (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    Subgroup K.toSubgroup :=
  (unramifiedDegreeHom D K f hf).toMonoidHom.ker

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
