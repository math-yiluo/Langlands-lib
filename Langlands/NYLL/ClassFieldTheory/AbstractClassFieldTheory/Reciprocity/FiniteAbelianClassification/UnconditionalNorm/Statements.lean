/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Compositum
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions

/-!
# NYLL M298.028–.029: unconditional compositum norm and order targets

Modified by Worker 535, 14 November 2026: extract the statements of
`FiniteAbelianSubextension.normSubgroup_compositum` and
`FiniteAbelianSubextension.le_iff_normSubgroup_le` from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, source lines 782–817.
Prefix the namespace with `Langlands.NYLL`, replace each theorem by a
Prop-valued definition with suffix `Statement`, and replace the source imports
by focused prerequisite modules. Spell out the source section parameters in
each declaration and retain the entire source telescope, including the unused
valuation and class-field-axiom arguments. See the paired Markdown for the
source map, published dependencies and every modification; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for attribution.
-/

namespace Langlands.NYLL.ClassFormation.FiniteAbelianSubextension

set_option linter.unusedVariables false in
/-- Target of the first displayed formula in finite abelian classification:
the norm subgroup of the compositum is the intersection of the norm subgroups. -/
def normSubgroup_compositumStatement
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    {D : DegreeData G} {A : Rep ℤ G}
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field) : Prop :=
  (L₁.compositum L₂).normSubgroup A =
    L₁.normSubgroup A ⊓ L₂.normSubgroup A

set_option linter.unusedVariables false in
/-- Target of the order-reversal assertion in finite abelian classification:
field inclusion is exactly reverse inclusion of norm subgroups. -/
def le_iff_normSubgroup_leStatement
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    {D : DegreeData G} {A : Rep ℤ G}
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field) : Prop :=
  L₁ ≤ L₂ ↔ L₂.normSubgroup A ≤ L₁.normSubgroup A

end Langlands.NYLL.ClassFormation.FiniteAbelianSubextension
