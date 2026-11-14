/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.Restriction.Definitions

/-!
# NYLL M298.010 and M298.017: restriction targets

Modified by Worker 458, 14 November 2026: state the source theorems M298.010
(`restriction_mk`, lines 248–259) and M298.017
(`eq_of_le_of_extensionQuotient_card_eq`, lines 377–414) of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709` as Prop-valued definitions.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to each theorem
name, keep each hypothesis as a binder of the definition and its conclusion as
the body, drop the proofs and the `@[simp]` attribute, replace the source
imports by the published imports these statements use, drop the unused section
variables and `open KummerTheory`, and install the two source local instances,
ported as `Langlands.NYLL.PortInternal.M298.d001` and
`Langlands.NYLL.PortInternal.M298.d002`, with `attribute [local instance]`.
The paired Markdown records every modification. See `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

namespace FiniteAbelianSubextension

attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
  Langlands.NYLL.PortInternal.M298.d002

/-- Target of `FiniteAbelianSubextension.restriction_mk`: restriction sends
the class of `k` in `L₂`'s quotient to the class of `k` in `L₁`'s quotient. -/
def restriction_mkStatement
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (k : K.toSubgroup) : Prop :=
  restriction h₁₂ (L₂.extensionQuotientMk k) =
    L₁.extensionQuotientMk k

-- Preserve the source hypothesis names even when the conclusion does not
-- mention them.
set_option linter.unusedVariables false in
/-- Target of `FiniteAbelianSubextension.eq_of_le_of_extensionQuotient_card_eq`:
if one finite abelian extension is contained in another and their actual
Galois quotients have the same finite cardinality, then the fields are
equal. -/
def eq_of_le_of_extensionQuotient_card_eqStatement
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (hcard : Nat.card L₂.extensionQuotient =
      Nat.card L₁.extensionQuotient) : Prop :=
  L₁ = L₂

end FiniteAbelianSubextension

end Langlands.NYLL.ClassFormation
