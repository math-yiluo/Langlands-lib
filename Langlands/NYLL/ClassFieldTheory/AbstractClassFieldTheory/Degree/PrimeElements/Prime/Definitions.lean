/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions

/-!
# Prime elements and the additive unit group

Modified by Worker 5264, 15 November 2026: extract M028.007 and M028.008 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source module import by the published
normalized-valuation and one-value modules. Universes, binders, docstrings and
bodies are unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- **the prime-element definition.** A prime element has normalized value `1`. -/
def IsPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G)
    (π : ambientFixedAddSubgroup A K.field) : Prop :=
  v.valuationAt K π = v.oneValue

/-- **the prime-element definition.** The additive form of the unit group
`U_K = {u | v_K(u)=0}`. -/
def unitAddSubgroup (v : ValuationData D A) (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  (v.valuationAt K).ker

end ValuationData

end

end Langlands.NYLL.ClassFormation
