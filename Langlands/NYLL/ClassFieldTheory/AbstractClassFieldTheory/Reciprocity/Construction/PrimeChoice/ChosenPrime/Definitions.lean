/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U018.Proofs

/-!
# The chosen prime element of a finite abstract field

Modified by Worker 5264, 15 November 2026: port the source definition
M030.001 `ValuationData.chosenPrimeElement` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL` and replace the source import by focused published imports.
The definition applies the theorem `v.normalizedValuation_surjective K`
(M025.027), whose proof is not published, to `v.oneValue`; it is replaced by
the source proof of that theorem
(`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`),
stated with `show`. In that proof the rewrite with
`v.normCompositeAt_range K` (M025.020, proof not published) is made with a
local `hrange` proved by the source proof of that theorem, the structure
field `v.norm_range K`. Since `Classical.choose` depends only on the
proposition, the chosen element is the source one. The docstring, the opens,
the variable declarations and the binders are unchanged. Omit the rest of
the source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

namespace ValuationData

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- A chosen prime element of a finite abstract field.  Later independence
lemmas show that the reciprocity class does not depend on this choice. -/
def chosenPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field :=
  Classical.choose
    ((show Function.Surjective (v.valuationAt K) by
      intro z
      have hzImage : (K.residueDegree D : ℕ) • z.1 ∈
          nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
        ⟨z.1, z.2, rfl⟩
      have hrange : (v.normCompositeAt K).range =
          nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
        v.norm_range K
      rw [← hrange] at hzImage
      obtain ⟨a, ha⟩ := hzImage
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change zHatDivide (K.residueDegree D : ℕ)
          (K.residueDegree D).property
            (v.normCompositeAtInResidueImage K a) = z.1
      have hsub : v.normCompositeAtInResidueImage K a =
          ⟨zHatMulNat (K.residueDegree D : ℕ) z.1, ⟨z.1, rfl⟩⟩ := by
        apply Subtype.ext
        change v.normCompositeAt K a =
          zHatMulNat (K.residueDegree D : ℕ) z.1
        exact ha
      rw [hsub]
      exact zHatDivide_zHatMulNat (K.residueDegree D : ℕ)
        (K.residueDegree D).property z.1) v.oneValue)

end ValuationData

end

end Langlands.NYLL.ClassFormation
