/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.Restriction.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.Restriction.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.U011.Proofs
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs

/-!
# NYLL M298.017: finite-quotient cardinal rigidity

Modified by Worker 261, 16 November 2026: extract M298.017 (lines 377–414)
from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, replace the original imports by the published target and
proof dependencies, state the result as the published Statement applied to
its complete source telescope, and expose that conclusion with an initial
`change`. Keep the original tactic proof after that line. Omit the unused
section variables, write its arbitrary universe as `u`, and install the
source local instances under their published names. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology KummerTheory

universe u

namespace FiniteAbelianSubextension

attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
  Langlands.NYLL.PortInternal.M298.d002

/-- Contained finite abelian subextensions with equally large Galois quotients
are equal. -/
theorem eq_of_le_of_extensionQuotient_card_eq
    {G : Type u} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (hcard : Nat.card L₂.extensionQuotient =
      Nat.card L₁.extensionQuotient) :
    eq_of_le_of_extensionQuotient_card_eqStatement h₁₂ hcard := by
  change L₁ = L₂
  let r := restriction h₁₂
  have hrSurjective : Function.Surjective r := by
    simpa [r, restriction] using
      L₁.extensionQuotientMulEquiv.symm.surjective.comp
        ((abstractReciprocityRestriction_surjective K L₁.field L₂.field
          h₁₂ L₁.below).comp
            L₂.extensionQuotientMulEquiv.surjective)
  have hrBijective : Function.Bijective r :=
    (Nat.bijective_iff_surjective_and_card r).2
      ⟨hrSurjective, hcard⟩
  apply le_antisymm h₁₂
  intro g hg
  let k : K.toSubgroup := ⟨g, L₁.below hg⟩
  have hrOne : r (L₂.extensionQuotientMk k) = 1 := by
    rw [show r (L₂.extensionQuotientMk k) =
      L₁.extensionQuotientMk k by exact restriction_mk h₁₂ k]
    apply L₁.extensionQuotientMulEquiv.injective
    rw [map_one, L₁.extensionQuotientMk_apply]
    apply (QuotientGroup.eq_one_iff k).2
    exact (mem_extensionSubgroup_iff K L₁.field L₁.below k).2 hg
  have hkOne : L₂.extensionQuotientMk k = 1 := by
    apply hrBijective.1
    simpa [r] using hrOne
  have hkOneRaw := congrArg L₂.extensionQuotientMulEquiv hkOne
  simp only [L₂.extensionQuotientMk_apply, map_one] at hkOneRaw
  exact (mem_extensionSubgroup_iff K L₂.field L₂.below k).1
    ((QuotientGroup.eq_one_iff k).1 hkOneRaw)

end FiniteAbelianSubextension

end Langlands.NYLL.ClassFormation
