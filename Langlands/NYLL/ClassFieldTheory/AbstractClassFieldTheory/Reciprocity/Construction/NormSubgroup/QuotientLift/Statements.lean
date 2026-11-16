/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.QuotientLift.Definitions

/-!
# Target: the maximal-unramified quotient lift on classes

Modified by Worker 5264, 15 November 2026: extract the statement of M029.036
from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source imports by the module of the
quotient lift (M029.035), which imports the published class map. Replace the
source theorem by a Prop-valued definition with the `Statement` suffix,
omitting its proof and its `@[simp]` attribute, and reword the declaration
docstring to describe the proposition. The opens, the variable declaration
and the binders are unchanged. Omit the rest of the source file. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

section maximalUnramifiedNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The proposition, from the source theorem
`maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass`, that the
quotient lift sends a maximal-unramified norm class back to its
representative. -/
def maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClassStatement
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) : Prop :=
    D.maximalUnramifiedNormQuotientLift A K L f hf
        (D.maximalUnramifiedNormClass A K L a) = f a

end DegreeData

end maximalUnramifiedNorms

end
end Langlands.NYLL.ClassFormation
