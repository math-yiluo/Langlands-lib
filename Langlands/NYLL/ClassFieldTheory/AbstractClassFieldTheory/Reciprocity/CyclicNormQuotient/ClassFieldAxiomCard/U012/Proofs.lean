/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 746, 16 November 2026 UTC:
Extract only the proof of M074.012 `additiveExtensionQuotient_card` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published ClassFieldAxiomCard.Statements
module and state the theorem as the published Statement applied to the
source parameter. Replace the citation of the unpublished M010.092
`FiniteAbstractExtension.extensionSubgroup_index_eq_degree` by the local
private lemma `additiveExtensionQuotient_card_index_eq_degree`, whose proof
is the source proof of M010.092 with its rewrite by the unpublished
definitional M010.088 `degree_coe` (source proof `rfl`) dropped. The calc
chain is otherwise the original one. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.ClassFieldAxiomCard.Statements

/-!
# The order of the Galois quotient of a finite extension

The exact proof that the additive form of the quotient `G_K / G_L` of a
finite abstract extension `L | K` has the extension degree as its order.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Local copy of the source proof of M010.092: the index of the represented
extension subgroup is the finite extension degree. -/
private theorem additiveExtensionQuotient_card_index_eq_degree
    (E : DegreeData.FiniteAbstractExtension G) :
    (extensionSubgroup E.base E.field E.below).index = (E.degree : ℕ) := by
  rw [Subgroup.index]
  rfl

/-- The additive Galois quotient has the extension degree as its order. -/
theorem additiveExtensionQuotient_card
    (E : DegreeData.FiniteAbstractExtension G) :
    additiveExtensionQuotient_cardStatement E := by
  calc
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
        Nat.card
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below) :=
      (Nat.card_congr
        (Additive.ofMul :
          (E.base.toSubgroup ⧸
              extensionSubgroup E.base E.field E.below) ≃
            Additive
              (E.base.toSubgroup ⧸
                extensionSubgroup E.base E.field E.below))).symm
    _ = (extensionSubgroup E.base E.field E.below).index :=
      (Subgroup.index_eq_card
        (extensionSubgroup E.base E.field E.below)).symm
    _ = (E.degree : ℕ) := additiveExtensionQuotient_card_index_eq_degree E

end

end Langlands.NYLL.ClassFormation
