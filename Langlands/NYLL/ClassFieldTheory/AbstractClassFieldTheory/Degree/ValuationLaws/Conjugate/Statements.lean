/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Conjugate.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FiniteAbstractFieldConjugate.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions

/-!
# Targets: conjugation preserves residue degrees and normalized valuations

Modified by Worker 5264, 15 November 2026: extract the statements of
M027.003, M027.005 and M027.006 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source imports by focused published
imports and the conjugate of a residue-finite field (M027.002). Replace each
source theorem by a Prop-valued definition with the `Statement` suffix,
omitting its proof, and reword the declaration docstrings to describe the
propositions. The opens, the variable declarations (used by M027.006; the
first two targets bind their own `G`) and the binders are unchanged. Omit
the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- The proposition, from the source theorem
`DegreeData.FiniteResidueAbstractField.residueDegree_conjugate`, that
conjugation preserves the positive absolute residue degree at the
residue-finite boundary. -/
def DegreeData.FiniteResidueAbstractField.residueDegree_conjugateStatement
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    Prop :=
    (K.conjugate σ).residueDegree = K.residueDegree

/-- The proposition, from the source theorem
`FiniteAbstractField.residueDegree_conjugate`, that conjugation preserves the
positive absolute residue degree. -/
def FiniteAbstractField.residueDegree_conjugateStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (K : FiniteAbstractField G)
    (D : DegreeData G) (σ : G) : Prop :=
    (K.conjugate σ).residueDegree D = K.residueDegree D

namespace ValuationData

/-- The proposition, from the source theorem `normalizedValuation_conjugate`
(conjugation compatibility of normalized valuations), that the normalized
valuations are compatible with conjugation: `v_{K^σ}(a^σ) = v_K(a)` (the
right-action notation). -/
def normalizedValuation_conjugateStatement [ContinuousMul G]
    (v : ValuationData D A) (K : FiniteAbstractField G) (σ : G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
    v.valuationAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) =
      v.valuationAt K a

end ValuationData

end

end Langlands.NYLL.ClassFormation
