/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Definitions

/-!
# NYLL M076: intermediate-extension subgroup and coset targets

Modified by Worker 4918: state the source theorems listed in the paired
Markdown from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
as Prop-valued definitions ending in `Statement`, with the source binders and
statements, under the namespace prefix `Langlands.NYLL`. The source section
instance `[IsTopologicalGroup G]` is written as an explicit binder of exactly
the two targets whose source theorems keep it, and `{K : ClosedSubgroup G}` is
bound in each target. Proofs and `simp` attributes are omitted. The paired
Markdown records every modification. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Target M076.002: membership in the intermediate subgroup is characterized
by membership of the underlying ambient element. -/
def mem_intermediateSubgroup_iffStatement {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (k : K.toSubgroup) : Prop :=
  k ∈ L.intermediateSubgroup S ↔ L.extensionQuotientMk k ∈ S

/-- Target M076.006: membership in the canonical coset is equality with its
quotient class. -/
def mem_intermediateCoset_iffStatement {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) : Prop :=
  x ∈ L.intermediateCoset q ↔
    L.extensionQuotientMk x = q

/-- Target M076.009: the inverse image of `S` is literally the finite union of
the `G_L` cosets indexed by the elements of `S`. -/
def intermediateSubgroup_eq_iUnion_cosetsStatement {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) : Prop :=
  (L.intermediateSubgroup S : Set K.toSubgroup) =
    ⋃ q ∈ (S : Set L.extensionQuotient), L.intermediateCoset q

/-- Target M076.011: every coset in the preceding union is closed: it is the
image of the closed subgroup `G_L ≤ G_K` under right translation. -/
def intermediateCoset_isClosedStatement [IsTopologicalGroup G]
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Prop :=
  IsClosed (L.intermediateCoset q)

/-- Target M076.012: closedness of the inverse image, proved by its finite
coset decomposition rather than postulated as a Galois-correspondence
property. -/
def intermediateSubgroup_isClosedStatement [IsTopologicalGroup G]
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Prop :=
  IsClosed (L.intermediateSubgroup S : Set K.toSubgroup)

set_option linter.unusedVariables false in
/-- Target M076.023: a normal subgroup `S ◁ G(L/K)` has normal inverse image
in `G_K`. -/
def intermediateSubgroup_normalStatement {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) : Prop :=
  (L.intermediateSubgroup S).Normal

/-- Target M076.034: mapping the inverse image of `S` back to `G(L/K)`
recovers `S` itself. -/
def intermediateSubgroup_map_quotient_eqStatement {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) : Prop :=
  (L.intermediateSubgroup S).map L.extensionQuotientMk = S

end FiniteGaloisSubextension

end
end Langlands.NYLL.ClassFormation
