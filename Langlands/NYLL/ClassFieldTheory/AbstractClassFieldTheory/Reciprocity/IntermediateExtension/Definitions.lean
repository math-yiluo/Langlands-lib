/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Mathlib.Topology.Algebra.Group.Basic

/-!
# NYLL M076: intermediate-extension subgroup, coset and upper-quotient data

Modified by Worker 4918: extract the source data and instance units listed in
the paired Markdown from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`,
prefix the namespace with `Langlands.NYLL`, replace the source module import by
the published finite Galois subextension data, and drop the unused
`open KummerTheory`. The paired Markdown records every modification. See
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inverse image in `G_K` of a subgroup of `G(L/K)`. -/
def intermediateSubgroup (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Subgroup K.toSubgroup := by
  exact S.comap L.extensionQuotientMk

/-- The `G_L`-coset classified by `q ∈ G(L/K)`, defined canonically as a
fiber of the quotient map.  In particular, its public definition does not
choose a representative of `q`. -/
def intermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  {x | L.extensionQuotientMk x = q}

/-- The third-isomorphism identification used in the normal-subextension
diagram: `G(L/K)/S ≃ G(M/K)`. -/
def upperQuotient (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Type _ :=
  L.extensionQuotient ⧸ S

/-- The upper quotient over an intermediate field carries its canonical group structure. -/
instance upperQuotient_groupInstance (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Group (L.upperQuotient S) := by
  change Group (L.extensionQuotient ⧸ S)
  infer_instance

/-- Comparison with the group-library presentation of the upper quotient. -/
def upperQuotientMulEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.upperQuotient S ≃* (L.extensionQuotient ⧸ S) :=
  MulEquiv.refl _

/-- The canonical projection to the named upper quotient. -/
def upperQuotientMk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →* L.upperQuotient S :=
  QuotientGroup.mk' S

end FiniteGaloisSubextension

end
end Langlands.NYLL.ClassFormation
