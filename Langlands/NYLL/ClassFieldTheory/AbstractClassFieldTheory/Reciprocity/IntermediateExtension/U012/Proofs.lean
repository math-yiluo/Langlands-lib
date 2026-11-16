/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U008.Proofs

/-!
# NYLL M076.012: the intermediate subgroup is closed

Modified by Worker 756, 16 November 2026: extract the proof of M076.012
`FiniteGaloisSubextension.intermediateSubgroup_isClosed` (lines 172–178) of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, and state the theorem as the published Statement applied to
the source parameters. The source cites M076.009
`intermediateSubgroup_eq_iUnion_cosets` and M076.011
`intermediateCoset_isClosed`, whose proofs are not yet in the Library; this
file proves both locally as private theorems under the non-conflicting names
`intermediateSubgroup_eq_iUnion_cosets_local` and
`intermediateCoset_isClosed_local`, the second by a preimage argument instead
of the source's representative image. The paired Markdown records every
modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Local copy of source M076.009: the inverse image of `S` is the union of
the `G_L` cosets indexed by the elements of `S`. -/
private theorem intermediateSubgroup_eq_iUnion_cosets_local
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S : Set K.toSubgroup) =
      ⋃ q ∈ (S : Set L.extensionQuotient), L.intermediateCoset q := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion₂.mpr ⟨L.extensionQuotientMk x, hx, rfl⟩
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨q, hqS, hxq⟩
    change L.extensionQuotientMk x ∈ S
    change L.extensionQuotientMk x = q at hxq
    rw [hxq]
    exact hqS

/-- Local version of source M076.011: the coset of class `q` is the preimage
of the closed subgroup `G_L` under left multiplication by `r⁻¹`, for any
representative `r` of `q`, hence closed. -/
private theorem intermediateCoset_isClosed_local [IsTopologicalGroup G]
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : IsClosed (L.intermediateCoset q) := by
  obtain ⟨r, hr⟩ :=
    QuotientGroup.mk'_surjective (extensionSubgroup K L.field L.below) q
  have hset : L.intermediateCoset q =
      (fun x : K.toSubgroup => r⁻¹ * x) ⁻¹'
        (extensionSubgroup K L.field L.below : Set K.toSubgroup) := by
    ext x
    change (QuotientGroup.mk x :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below) = q ↔
      r⁻¹ * x ∈ extensionSubgroup K L.field L.below
    rw [← hr, eq_comm]
    exact QuotientGroup.eq
  rw [hset]
  exact (Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed
    K L.field L.below).preimage (continuous_const.mul continuous_id)

/-- Closedness of the inverse image, proved by its finite coset
decomposition rather than postulated as a Galois-correspondence property. -/
theorem intermediateSubgroup_isClosed [IsTopologicalGroup G]
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    intermediateSubgroup_isClosedStatement L S := by
  change IsClosed (L.intermediateSubgroup S : Set K.toSubgroup)
  rw [intermediateSubgroup_eq_iUnion_cosets_local]
  have hfinite : (S : Set L.extensionQuotient).Finite := Set.toFinite _
  exact hfinite.isClosed_biUnion fun q _ => intermediateCoset_isClosed_local L q

end FiniteGaloisSubextension

end
end Langlands.NYLL.ClassFormation
