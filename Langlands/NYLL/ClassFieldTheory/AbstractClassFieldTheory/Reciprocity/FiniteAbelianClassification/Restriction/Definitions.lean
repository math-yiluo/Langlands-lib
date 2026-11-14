/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification.QuotientInstances.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions

/-!
# NYLL M298.009: restriction between finite abelian subextensions

Modified by Worker 458, 14 November 2026: extract the source definition
M298.009 (lines 235–246) of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by the published imports this
definition uses, drop the unused section variables and `open KummerTheory`, and
install the two source local instances, ported as
`Langlands.NYLL.PortInternal.M298.d001` and `Langlands.NYLL.PortInternal.M298.d002`,
with `attribute [local instance]`, so that they are in scope as in the source.
Binders, binder kinds, the result type and the body are otherwise unchanged.
The paired Markdown records every modification. See `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

namespace FiniteAbelianSubextension

attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
  Langlands.NYLL.PortInternal.M298.d002

/-- Restriction along an inclusion of finite abelian subextensions.  The
proof-dependent raw quotient map is transported through the two named
quotient boundaries here and nowhere in its callers. -/
def restriction
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂) :
    L₂.extensionQuotient →* L₁.extensionQuotient := by
  letI : (extensionSubgroup K L₁.field L₁.below).Normal := L₁.normal
  letI : (extensionSubgroup K L₂.field L₂.below).Normal := L₂.normal
  exact L₁.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction K L₁.field L₂.field h₁₂ L₁.below).comp
      L₂.extensionQuotientMulEquiv.toMonoidHom)

end FiniteAbelianSubextension

end Langlands.NYLL.ClassFormation
