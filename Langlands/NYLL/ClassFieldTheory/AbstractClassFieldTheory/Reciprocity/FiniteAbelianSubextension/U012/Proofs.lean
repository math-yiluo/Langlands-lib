/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 467 (2026-11-14): extract only the proof of M296.012 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean
(lines 119–125) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published Statements module of
Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
and state the protected theorem as that module's
`extensionQuotient_inductionOnStatement` applied to the source binders. The
source proof calls `FiniteGaloisSubextension.extensionQuotient_inductionOn`
(M040.016), which is not in the Library; after `unfold`, the proof instead
applies Mathlib's `Quotient.inductionOn'` directly, since the abelian
quotient is by definition the finite Galois quotient group and the named
projection is `QuotientGroup.mk'`. The noncomputable section and the
`open CyclicCohomology KummerTheory` are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Statements

/-!
# Induction on a finite abelian extension quotient (NYLL M296.012)

For a finite abelian subextension `L` of `K`, a proposition about elements of
the quotient `G(L/K)` holds everywhere once it holds on the image of every
`k ∈ K` under the canonical projection.
-/

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- Eliminate an abelian extension quotient without choosing a representative. -/
protected theorem extensionQuotient_inductionOn
    (L : FiniteAbelianSubextension K)
    {motive : L.extensionQuotient → Prop} (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) :
    L.extensionQuotient_inductionOnStatement (motive := motive) q mk := by
  unfold FiniteAbelianSubextension.extensionQuotient_inductionOnStatement
  exact Quotient.inductionOn' q mk

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
